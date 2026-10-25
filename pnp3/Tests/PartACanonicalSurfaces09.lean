import Tests.PartACanonicalABI
import Tests.PartAG2InterfaceTests

/-! Infrastructure: mechanical literal restatements of this exact original API.
Proof terms are reused; these are not independently authored correctness proofs.
Type pins, theorem mirrors and direct roots remain separate manifests. -/
set_option autoImplicit false

-- Independent literal expected type for NormalClockClosure.Audit.pin_Bridge.
noncomputable def PartACanonical.Types.p0509 :
(∀ (_v0 : (@Nat)),
(Sort 0)) := by
  exact @NormalClockClosure.Audit.pin_Bridge

-- Independent literal expected type for NormalClockClosure.Audit.pin_degree.
noncomputable def PartACanonical.Types.p0510 :
(∀ (_v0 : (@Nat)),
(@Nat)) := by
  exact @NormalClockClosure.Audit.pin_degree

-- Independent literal expected type for NormalClockClosure.Target.Bridge.
noncomputable def PartACanonical.Types.p0511 :
(∀ (_v0 : (@Nat)),
(Sort 0)) := by
  exact @NormalClockClosure.Target.Bridge

-- Independent literal expected type for NormalClockClosure.bridge.
noncomputable def PartACanonical.Types.p0512 :
(∀ (_v0 : (@Nat)),
(@NormalClockClosure.Target.Bridge _v0)) := by
  exact @NormalClockClosure.bridge

-- Complete literal proposition for NormalClockClosure.bridge; original proof reused.
theorem PartACanonical.Surface.m0298 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(let _v3 : (@Nat) := (@RawCallerClosure.allocation _v0 _v1);
(let _v4 : (@Pnp3.Complexity.Uniform.V1.UniformTM) := (@NormalFinalClosure.machine2 _v0);
(let _v5 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v4 _v1 _v3 _v2);
(let _v6 : (@Pnp3.Complexity.Uniform.V1.UniformTM) := (@RawCallerClosure.machine _v0);
(let _v7 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v3) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v6 _v1 _v3 _v2);
(let _v8 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0))) :=
  (@RawCallerClosure.callerState _v0 (@PhysicalCallerClosure.rowsDone _v0));
(let _v9 : (∀ (_v9 : (@Bool)),
(@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0)))) := (fun (_v9 : (@Bool)) =>
(@RawCallerClosure.old _v0 (@CertificateGuardClosure.old _v0 (@TotalIngressClosure.old _v0 (@BodyIngress.old _v0
  (@CarryWindow.embed _v0 (@CanonicalLeaf.result _v0 _v9)))))));
(let _v10 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.polyClock (@NormalClockClosure.degree _v0) _v1);
(@Exists.{(0 + 1)} (@Nat) (fun (_v11 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v12 : (@Nat)) =>
(@Exists.{0} (@LE.le.{0} (@Nat) (@instLENat) _v3 _v10) (fun (_v13 : (@LE.le.{0} (@Nat) (@instLENat) _v3 _v10)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v11 _v12) (@And (@LE.le.{0} (@Nat) (@instLENat) _v12 (@HMul.hMul.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (17592186044416 : Nat) (@instOfNatNat (17592186044416 : Nat))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat))))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 :
  Nat)))))) (@And (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v12 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v3) (@And (@LE.le.{0} (@Nat)
  (@instLENat) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (17592186044416 : Nat) (@instOfNatNat
  (17592186044416 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))))) _v10) (@And (∀ (_v14 : (@Nat)),
(∀ (_v15 : (@LE.le.{0} (@Nat) (@instLENat) _v14 _v12)),
(@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3
  _v14 _v5))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1
  _v3)))) (@And (∀ (_v14 : (@Nat)),
(∀ (_v15 : (@LE.le.{0} (@Nat) (@instLENat) _v3 _v14)),
(@And (∀ (_v16 : (@Nat)),
(∀ (_v17 : (@LE.le.{0} (@Nat) (@instLENat) _v16 _v12)),
(@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3 _v16 _v5)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v14 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v14
  _v16 (@Pnp3.Complexity.Uniform.V1.initialConfig _v4 _v1 _v14 _v2)))) (@And (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v14)) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v14 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v14
  _v16 (@Pnp3.Complexity.Uniform.V1.initialConfig _v4 _v1 _v14 _v2)))
  (@Pnp3.Complexity.Uniform.V1.FixedPairParser.tapeEmbed _v1 _v3 _v14 _v15 (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3
  _v16 _v5)))) (@And (∀ (_v18 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v14 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v14
  _v16 (@Pnp3.Complexity.Uniform.V1.initialConfig _v4 _v1 _v14 _v2))
  (@Pnp3.Complexity.Uniform.V1.FixedPairParser.tapeEmbed _v1 _v3 _v14 _v15 _v18)) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3
  _v16 _v5) _v18))) (@And (∀ (_v18 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v14))),
(∀ (_v19 : (@LE.le.{0} (@Nat) (@instLENat) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v14) _v18))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v14 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v14
  _v16 (@Pnp3.Complexity.Uniform.V1.initialConfig _v4 _v1 _v14 _v2)) _v18) (@Option.none.{0} (@Bool))))) (@And (@LE.le.{0}
  (@Nat) (@instLENat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3
  _v16 _v5))) _v12) (@LE.le.{0} (@Nat) (@instLENat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v14)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v14
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v14 _v16 (@Pnp3.Complexity.Uniform.V1.initialConfig _v4 _v1 _v14
  _v2)))) _v12)))))))) (@And (∀ (_v16 : (@Nat)),
(∀ (_v17 : (@LT.lt.{0} (@Nat) (@instLTNat) _v16 _v12)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v14
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v14 _v16 (@Pnp3.Complexity.Uniform.V1.initialConfig _v4 _v1 _v14
  _v2))) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v4)) (@And (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v14 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v14
  _v16 (@Pnp3.Complexity.Uniform.V1.initialConfig _v4 _v1 _v14 _v2))) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v4))
  (∀ (_v18 : (@Bool)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v14 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v14
  _v16 (@Pnp3.Complexity.Uniform.V1.initialConfig _v4 _v1 _v14 _v2))) (@NormalFinalClosure.old2 _v0 (@_v9 _v18)))))))) (∀
  (_v16 : (@Nat)),
(∀ (_v17 : (@LE.le.{0} (@Nat) (@instLENat) _v12 _v16)),
(∀ (_v18 : (@Or (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3 _v12 _v5)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v4))
  (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3
  _v12 _v5)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v4)))),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v14)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v14 _v16 (@Pnp3.Complexity.Uniform.V1.initialConfig _v4 _v1 _v14
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v14 _v12 (@Pnp3.Complexity.Uniform.V1.initialConfig _v4 _v1
  _v14 _v2)))))))))) (@And (∀ (_v14 : (@Bool)),
(∀ (_v15 : (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3 _v12 _v5)) (@ite.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4)) (@Eq.{(0 + 1)} (@Bool) _v14 (@Bool.true)) (@instDecidableEqBool
  _v14 (@Bool.true)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v4) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject
  _v4)))),
(@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1
  _v10) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v10 _v10 (@Pnp3.Complexity.Uniform.V1.initialConfig _v4 _v1
  _v10 _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v10 _v12 (@Pnp3.Complexity.Uniform.V1.initialConfig _v4
  _v1 _v10 _v2))) (@And (@Pnp3.Complexity.Uniform.V1.DecidesAt _v4 _v1 _v10 _v10 _v2 _v14)
  (@Pnp3.Complexity.Uniform.V1.DecidesWithin _v4 _v1 _v10 _v2 _v14))))) (@And (∀ (_v14 : (@Nat)),
(∀ (_v15 : (@LE.le.{0} (@Nat) (@instLENat) _v14 _v11)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@NormalFinalClosure.machine2 _v0)) _v1 _v3) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@NormalFinalClosure.machine2
  _v0) _v1 _v3 _v14 _v5) (@NormalFinalClosure.config2 _v0 _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v3
  _v14 _v7))))) (@And (∀ (_v14 : (@Nat)),
(∀ (_v15 : (@LE.le.{0} (@Nat) (@instLENat) _v14 _v11)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v3
  _v14 _v7)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v6)))) (@And (∀ (_v14 : (@Nat)),
(∀ (_v15 : (@LT.lt.{0} (@Nat) (@instLTNat) _v14 _v11)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v3 _v14 _v7)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v6))
  (@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v3 _v14 _v7)) _v8) (∀ (_v16 : (@Bool)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v3
  _v14 _v7)) (@_v9 _v16))))))) (@And (∀ (_v14 : (@Nat)),
(∀ (_v15 : (@LT.lt.{0} (@Nat) (@instLTNat) _v14 _v12)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2 _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@NormalFinalClosure.machine2 _v0)) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@NormalFinalClosure.machine2
  _v0) _v1 _v3 _v14 _v5)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@NormalFinalClosure.machine2 _v0))) (@And
  (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2 _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@NormalFinalClosure.machine2 _v0)) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@NormalFinalClosure.machine2
  _v0) _v1 _v3 _v14 _v5)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@NormalFinalClosure.machine2 _v0))) (∀ (_v16 :
  (@Bool)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2 _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@NormalFinalClosure.machine2 _v0)) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@NormalFinalClosure.machine2
  _v0) _v1 _v3 _v14 _v5)) (@NormalFinalClosure.old2 _v0 (@_v9 _v16)))))))) (@Or (@And (@Eq.{(0 + 1)} (@Nat) _v12 _v11)
  (@And (@Exists.{(0 + 1)} (@Bool) (fun (_v14 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v3
  _v11 _v7)) (@_v9 _v14)))) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2 _v0)) _v1 _v3)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@NormalFinalClosure.machine2 _v0) _v1 _v3 _v12 _v5)
  (@NormalFinalClosure.config2 _v0 _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v3 _v11 _v7))))) (@Or (@And
  (@Eq.{(0 + 1)} (@Nat) _v12 _v11) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v3 _v11 _v7)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v6))
  (@And (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.encodedRelationLanguage
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0) _v1 _v2) (@Bool.false)) (@Eq.{(0 +
  1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2
  _v0)) _v1 _v3) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@NormalFinalClosure.machine2 _v0) _v1 _v3 _v12 _v5)
  (@NormalFinalClosure.config2 _v0 _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v3 _v11 _v7))))))
  (@Exists.{(0 + 1)} (@Nat) (fun (_v14 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v15 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v14) (fun (_v16 : (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v14)) =>
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v15) (fun (_v17 : (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v15)) =>
(@Exists.{0} (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v14 _v15) _v1) (fun (_v18 :
  (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v14 _v15) _v1)) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.decodePair _v1 _v2) (@Option.some.{0} (@Prod.{0, 0} (@Sigma.{0, 0} (@Nat) (fun
  (_v19 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v19))) (@Sigma.{0, 0} (@Nat) (fun (_v19 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v19)))) (@Prod.mk.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v19 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v19))) (@Sigma.{0, 0} (@Nat) (fun (_v19 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v19))) (@Sigma.mk.{0, 0} (@Nat) (fun (_v19 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v19)) _v14 _v16) (@Sigma.mk.{0, 0} (@Nat) (fun (_v19 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v19)) _v15 _v17)))) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v1) _v2 (@Eq.rec.{(0 + 1), (0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v14 _v15) (fun (_v19 :
  (@Nat)) =>
(fun (_v20 : (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v14 _v15) _v19)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v19))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v14 _v15 _v16 _v17)
  _v1 _v18)) (@And (@Eq.{(0 + 1)} (@Nat) _v15 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v14 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Exists.{(0 + 1)} (@Nat) (fun (_v19
  : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v20 : (@Nat)) =>
(@And (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.tagMatches (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 _v15) (@Fin.append.{(0 + 1)} _v14 _v15 (@Bool) _v16 _v17))
  (@Bool.true)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Nat))
  (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros? (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 _v15) (@Fin.append.{(0 + 1)} _v14 _v15 (@Bool) _v16 _v17)) (@Option.some.{0}
  (@Nat) _v20)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Nat) (@Nat)))
  (@Pnp4.Frontier.ContractExpansion.contentHeader? (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v14 _v15) (@Fin.append.{(0 + 1)} _v14 _v15 (@Bool) _v16 _v17)) (@Option.some.{0} (@Prod.{0, 0} (@Nat)
  (@Nat)) (@Prod.mk.{0, 0} (@Nat) (@Nat) _v19 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v20) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))) (let _v21 :
  (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 _v15);
(let _v22 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v1);
(let _v23 : (@Nat) := (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v21 (@Min.min.{0}
  (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v20)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v19)) _v21));
(let _v24 : (@Nat) := (@Cursor.Target.W _v0 _v19);
(@And (@LT.lt.{0} (@Nat) (@instLTNat) (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v20))
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v19)) _v21) _v21) (@And (@LE.le.{0}
  (@Nat) (@instLENat) (@Pnp4.Frontier.ContractExpansion.bitLength _v19) _v23) (@And (@LE.le.{0} (@Nat) (@instLENat) _v24
  _v23) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v3 _v11 _v7)) _v8) (@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v21 _v20)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v19) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3)) (fun (_v25 : (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v21 _v20)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v19) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3))) =>
(@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3)) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v3
  _v11 _v7)) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v21 _v20) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))
  _v19) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v25)) (@Exists.{(0 + 1)} (@Bool) (fun (_v26 :
  (@Bool)) =>
(@And (@Eq.{(0 + 1)} (@Bool) _v26 (@Pnp3.Complexity.Uniform.V1.encodedRelationLanguage
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0) _v1 _v2)) (@And (@Eq.{(0 + 1)}
  (@Bool) _v26 (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v14 _v15 _v16 _v17))
  (@And (@Iff (@Eq.{(0 + 1)} (@Bool) _v26 (@Bool.true)) (@Exists.{(0 + 1)} (@Nat) (fun (_v27 : (@Nat)) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@Pnp4.Frontier.ContractExpansion.readNatBE (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v20)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v19))
  (@Pnp4.Frontier.ContractExpansion.bitLength _v24)) _v24) (@Pnp4.Frontier.ContractExpansion.padWord (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 _v15) (@Fin.append.{(0 + 1)} _v14 _v15 (@Bool) _v16 _v17)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat)
  (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v20)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v19)) (@Pnp4.Frontier.ContractExpansion.bitLength _v24)) _v24)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v20))
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v19))
  (@Pnp4.Frontier.ContractExpansion.bitLength _v24)) (@Option.some.{0} (@Nat) _v27)) (@And (@LE.le.{0} (@Nat) (@instLENat)
  _v27 _v24) (@And (∀ (_v28 : (@Nat)),
(∀ (_v29 : (@LT.lt.{0} (@Nat) (@instLTNat) _v28 _v27)),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 _v15) (@Fin.append.{(0 + 1)} _v14 _v15 (@Bool) _v16 _v17) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 :
  Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))) _v20)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v19))
  (@Pnp4.Frontier.ContractExpansion.bitLength _v24)) _v28)) (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 _v15) (@Fin.append.{(0 + 1)} _v14 _v15 (@Bool) _v16
  _v17) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v20)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v19))
  (@Pnp4.Frontier.ContractExpansion.bitLength _v24)) _v24) _v28))))) (∀ (_v28 : (@Nat)),
(∀ (_v29 : (@LE.le.{0} (@Nat) (@instLENat) _v27 _v28)),
(∀ (_v30 : (@LT.lt.{0} (@Nat) (@instLTNat) _v28 _v24)),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 _v15) (@Fin.append.{(0 + 1)} _v14 _v15 (@Bool) _v16 _v17) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 :
  Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))) _v20)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v19))
  (@Pnp4.Frontier.ContractExpansion.bitLength _v24)) _v28)) (@Bool.false))))))))))) (@Eq.{(0 + 1)}
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2
  _v0)) _v1 _v3) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@NormalFinalClosure.machine2 _v0) _v1 _v3 _v12 _v5)
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2
  _v0)) _v1 _v3 (@ite.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2
  _v0))) (@Eq.{(0 + 1)} (@Bool) _v26 (@Bool.true)) (@instDecidableEqBool _v26 (@Bool.true))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@NormalFinalClosure.machine2 _v0))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@NormalFinalClosure.machine2 _v0))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v21 _v20) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v19) (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v25) (@NormalFinalClosure.Target.cleared _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v3 _v11 _v7)) _v22 _v23
  _v19))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @NormalClockClosure.bridge

-- Independent literal expected type for NormalClockClosure.bridge_full.
noncomputable def PartACanonical.Types.p0513 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (∀ (_v2 : (@Fin _v1)),
(@Bool))),
(let _v3 : (@Nat) := (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@HMul.hMul.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (1099511627776 : Nat)
  (@instOfNatNat (1099511627776 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))));
(let _v4 : (@Pnp3.Complexity.Uniform.V1.UniformTM) := (@NormalFinalClosure.machine2 _v0);
(let _v5 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v4 _v1 _v3 _v2);
(let _v6 : (@Pnp3.Complexity.Uniform.V1.UniformTM) := (@RawCallerClosure.machine _v0);
(let _v7 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v3) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v6 _v1 _v3 _v2);
(let _v8 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0))) :=
  (@RawCallerClosure.callerState _v0 (@PhysicalCallerClosure.rowsDone _v0));
(let _v9 : (∀ (_v9 : (@Bool)),
(@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0)))) := (fun (_v9 : (@Bool)) =>
(@RawCallerClosure.old _v0 (@CertificateGuardClosure.old _v0 (@TotalIngressClosure.old _v0 (@BodyIngress.old _v0
  (@CarryWindow.embed _v0 (@CanonicalLeaf.result _v0 _v9)))))));
(let _v10 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v1
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4503599627370496 : Nat) (@instOfNatNat
  (4503599627370496 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 :
  Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4503599627370496 : Nat) (@instOfNatNat
  (4503599627370496 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 :
  Nat)))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v11 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v12 : (@Nat)) =>
(@Exists.{0} (@LE.le.{0} (@Nat) (@instLENat) _v3 _v10) (fun (_v13 : (@LE.le.{0} (@Nat) (@instLENat) _v3 _v10)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v11 _v12) (@And (@LE.le.{0} (@Nat) (@instLENat) _v12 (@HMul.hMul.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (17592186044416 : Nat) (@instOfNatNat (17592186044416 : Nat))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat))))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 :
  Nat)))))) (@And (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v12 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v3) (@And (@LE.le.{0} (@Nat)
  (@instLENat) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (17592186044416 : Nat) (@instOfNatNat
  (17592186044416 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))))) _v10) (@And (∀ (_v14 : (@Nat)),
(∀ (_v15 : (@LE.le.{0} (@Nat) (@instLENat) _v14 _v12)),
(@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3
  _v14 _v5))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1
  _v3)))) (@And (∀ (_v14 : (@Nat)),
(∀ (_v15 : (@LE.le.{0} (@Nat) (@instLENat) _v3 _v14)),
(@And (∀ (_v16 : (@Nat)),
(∀ (_v17 : (@LE.le.{0} (@Nat) (@instLENat) _v16 _v12)),
(@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3 _v16 _v5)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v14 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v14
  _v16 (@Pnp3.Complexity.Uniform.V1.initialConfig _v4 _v1 _v14 _v2)))) (@And (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v14)) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v14 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v14
  _v16 (@Pnp3.Complexity.Uniform.V1.initialConfig _v4 _v1 _v14 _v2)))
  (@Pnp3.Complexity.Uniform.V1.FixedPairParser.tapeEmbed _v1 _v3 _v14 _v15 (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3
  _v16 _v5)))) (@And (∀ (_v18 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v14 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v14
  _v16 (@Pnp3.Complexity.Uniform.V1.initialConfig _v4 _v1 _v14 _v2))
  (@Pnp3.Complexity.Uniform.V1.FixedPairParser.tapeEmbed _v1 _v3 _v14 _v15 _v18)) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3
  _v16 _v5) _v18))) (@And (∀ (_v18 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v14))),
(∀ (_v19 : (@LE.le.{0} (@Nat) (@instLENat) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v14) _v18))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v14 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v14
  _v16 (@Pnp3.Complexity.Uniform.V1.initialConfig _v4 _v1 _v14 _v2)) _v18) (@Option.none.{0} (@Bool))))) (@And (@LE.le.{0}
  (@Nat) (@instLENat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3
  _v16 _v5))) _v12) (@LE.le.{0} (@Nat) (@instLENat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v14)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v14
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v14 _v16 (@Pnp3.Complexity.Uniform.V1.initialConfig _v4 _v1 _v14
  _v2)))) _v12)))))))) (@And (∀ (_v16 : (@Nat)),
(∀ (_v17 : (@LT.lt.{0} (@Nat) (@instLTNat) _v16 _v12)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v14
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v14 _v16 (@Pnp3.Complexity.Uniform.V1.initialConfig _v4 _v1 _v14
  _v2))) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v4)) (@And (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v14 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v14
  _v16 (@Pnp3.Complexity.Uniform.V1.initialConfig _v4 _v1 _v14 _v2))) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v4))
  (∀ (_v18 : (@Bool)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v14 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v14
  _v16 (@Pnp3.Complexity.Uniform.V1.initialConfig _v4 _v1 _v14 _v2))) (@NormalFinalClosure.old2 _v0 (@_v9 _v18)))))))) (∀
  (_v16 : (@Nat)),
(∀ (_v17 : (@LE.le.{0} (@Nat) (@instLENat) _v12 _v16)),
(∀ (_v18 : (@Or (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3 _v12 _v5)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v4))
  (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3
  _v12 _v5)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v4)))),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v14)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v14 _v16 (@Pnp3.Complexity.Uniform.V1.initialConfig _v4 _v1 _v14
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v14 _v12 (@Pnp3.Complexity.Uniform.V1.initialConfig _v4 _v1
  _v14 _v2)))))))))) (@And (∀ (_v14 : (@Bool)),
(∀ (_v15 : (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3 _v12 _v5)) (@ite.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4)) (@Eq.{(0 + 1)} (@Bool) _v14 (@Bool.true)) (@instDecidableEqBool
  _v14 (@Bool.true)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v4) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject
  _v4)))),
(@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1
  _v10) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v10 _v10 (@Pnp3.Complexity.Uniform.V1.initialConfig _v4 _v1
  _v10 _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v10 _v12 (@Pnp3.Complexity.Uniform.V1.initialConfig _v4
  _v1 _v10 _v2))) (@And (@Pnp3.Complexity.Uniform.V1.DecidesAt _v4 _v1 _v10 _v10 _v2 _v14)
  (@Pnp3.Complexity.Uniform.V1.DecidesWithin _v4 _v1 _v10 _v2 _v14))))) (@And (∀ (_v14 : (@Nat)),
(∀ (_v15 : (@LE.le.{0} (@Nat) (@instLENat) _v14 _v11)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3 _v14 _v5) (@NormalFinalClosure.config2 _v0 _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v3 _v14 _v7))))) (@And (∀ (_v14 : (@Nat)),
(∀ (_v15 : (@LE.le.{0} (@Nat) (@instLENat) _v14 _v11)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v3
  _v14 _v7)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v6)))) (@And (∀ (_v14 : (@Nat)),
(∀ (_v15 : (@LT.lt.{0} (@Nat) (@instLTNat) _v14 _v11)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v3 _v14 _v7)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v6))
  (@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v3 _v14 _v7)) _v8) (∀ (_v16 : (@Bool)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v3
  _v14 _v7)) (@_v9 _v16))))))) (@And (∀ (_v14 : (@Nat)),
(∀ (_v15 : (@LT.lt.{0} (@Nat) (@instLTNat) _v14 _v12)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3 _v14 _v5)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v4))
  (@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3 _v14 _v5)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v4)) (∀
  (_v16 : (@Bool)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3
  _v14 _v5)) (@NormalFinalClosure.old2 _v0 (@_v9 _v16)))))))) (@Or (@And (@Eq.{(0 + 1)} (@Nat) _v12 _v11) (@And
  (@Exists.{(0 + 1)} (@Bool) (fun (_v14 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v3
  _v11 _v7)) (@_v9 _v14)))) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3
  _v12 _v5) (@NormalFinalClosure.config2 _v0 _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v3 _v11 _v7)))))
  (@Or (@And (@Eq.{(0 + 1)} (@Nat) _v12 _v11) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  _v6)) (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v3 _v11 _v7)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v6))
  (@And (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.encodedRelationLanguage
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0) _v1 _v2) (@Bool.false)) (@Eq.{(0 +
  1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3 _v12 _v5) (@NormalFinalClosure.config2 _v0 _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v3 _v11 _v7)))))) (@Exists.{(0 + 1)} (@Nat) (fun (_v14 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v15 : (@Nat)) =>
(@Exists.{(0 + 1)} (∀ (_v16 : (@Fin _v14)),
(@Bool)) (fun (_v16 : (∀ (_v16 : (@Fin _v14)),
(@Bool))) =>
(@Exists.{(0 + 1)} (∀ (_v17 : (@Fin _v15)),
(@Bool)) (fun (_v17 : (∀ (_v17 : (@Fin _v15)),
(@Bool))) =>
(@Exists.{0} (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v14 _v15) _v1) (fun (_v18 :
  (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v14 _v15) _v1)) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.decodePair _v1 _v2) (@Option.some.{0} (@Prod.{0, 0} (@Sigma.{0, 0} (@Nat) (fun
  (_v19 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v19))) (@Sigma.{0, 0} (@Nat) (fun (_v19 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v19)))) (@Prod.mk.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v19 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v19))) (@Sigma.{0, 0} (@Nat) (fun (_v19 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v19))) (@Sigma.mk.{0, 0} (@Nat) (fun (_v19 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v19)) _v14 _v16) (@Sigma.mk.{0, 0} (@Nat) (fun (_v19 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v19)) _v15 _v17)))) (@And (@Eq.{(0 + 1)} (∀ (_v19 : (@Fin _v1)),
(@Bool)) _v2 (@Eq.rec.{(0 + 1), (0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v14 _v15) (fun
  (_v19 : (@Nat)) =>
(fun (_v20 : (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v14 _v15) _v19)) =>
(∀ (_v21 : (@Fin _v19)),
(@Bool)))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v14 _v15 _v16 _v17) _v1 _v18)) (@And (@Eq.{(0 + 1)}
  (@Nat) _v15 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Exists.{(0 + 1)} (@Nat) (fun (_v19 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v20 : (@Nat)) =>
(@And (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.tagMatches (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 _v15) (@Fin.append.{(0 + 1)} _v14 _v15 (@Bool) _v16 _v17))
  (@Bool.true)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Nat))
  (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros? (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 _v15) (@Fin.append.{(0 + 1)} _v14 _v15 (@Bool) _v16 _v17)) (@Option.some.{0}
  (@Nat) _v20)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Nat) (@Nat)))
  (@Pnp4.Frontier.ContractExpansion.contentHeader? (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v14 _v15) (@Fin.append.{(0 + 1)} _v14 _v15 (@Bool) _v16 _v17)) (@Option.some.{0} (@Prod.{0, 0} (@Nat)
  (@Nat)) (@Prod.mk.{0, 0} (@Nat) (@Nat) _v19 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v20) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))) (let _v21 :
  (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 _v15);
(let _v22 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v1);
(let _v23 : (@Nat) := (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v21 (@Min.min.{0}
  (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v20)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v19)) _v21));
(let _v24 : (@Nat) := (@Cursor.Target.W _v0 _v19);
(@And (@LT.lt.{0} (@Nat) (@instLTNat) (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v20))
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v19)) _v21) _v21) (@And (@LE.le.{0}
  (@Nat) (@instLENat) (@Pnp4.Frontier.ContractExpansion.bitLength _v19) _v23) (@And (@LE.le.{0} (@Nat) (@instLENat) _v24
  _v23) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v3 _v11 _v7)) _v8) (@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v21 _v20)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v19) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3)) (fun (_v25 : (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v21 _v20)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v19) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3))) =>
(@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3)) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v3
  _v11 _v7)) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v21 _v20) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))
  _v19) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v25)) (@Exists.{(0 + 1)} (@Bool) (fun (_v26 :
  (@Bool)) =>
(@And (@Eq.{(0 + 1)} (@Bool) _v26 (@Pnp3.Complexity.Uniform.V1.encodedRelationLanguage
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0) _v1 _v2)) (@And (@Eq.{(0 + 1)}
  (@Bool) _v26 (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v14 _v15 _v16 _v17))
  (@And (@Iff (@Eq.{(0 + 1)} (@Bool) _v26 (@Bool.true)) (@Exists.{(0 + 1)} (@Nat) (fun (_v27 : (@Nat)) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@Pnp4.Frontier.ContractExpansion.readNatBE (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v20)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v19))
  (@Pnp4.Frontier.ContractExpansion.bitLength _v24)) _v24) (@Pnp4.Frontier.ContractExpansion.padWord (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 _v15) (@Fin.append.{(0 + 1)} _v14 _v15 (@Bool) _v16 _v17)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat)
  (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v20)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v19)) (@Pnp4.Frontier.ContractExpansion.bitLength _v24)) _v24)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v20))
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v19))
  (@Pnp4.Frontier.ContractExpansion.bitLength _v24)) (@Option.some.{0} (@Nat) _v27)) (@And (@LE.le.{0} (@Nat) (@instLENat)
  _v27 _v24) (@And (∀ (_v28 : (@Nat)),
(∀ (_v29 : (@LT.lt.{0} (@Nat) (@instLTNat) _v28 _v27)),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 _v15) (@Fin.append.{(0 + 1)} _v14 _v15 (@Bool) _v16 _v17) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 :
  Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))) _v20)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v19))
  (@Pnp4.Frontier.ContractExpansion.bitLength _v24)) _v28)) (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 _v15) (@Fin.append.{(0 + 1)} _v14 _v15 (@Bool) _v16
  _v17) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v20)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v19))
  (@Pnp4.Frontier.ContractExpansion.bitLength _v24)) _v24) _v28))))) (∀ (_v28 : (@Nat)),
(∀ (_v29 : (@LE.le.{0} (@Nat) (@instLENat) _v27 _v28)),
(∀ (_v30 : (@LT.lt.{0} (@Nat) (@instLTNat) _v28 _v24)),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 _v15) (@Fin.append.{(0 + 1)} _v14 _v15 (@Bool) _v16 _v17) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 :
  Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))) _v20)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v19))
  (@Pnp4.Frontier.ContractExpansion.bitLength _v24)) _v28)) (@Bool.false))))))))))) (@Eq.{(0 + 1)}
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3 _v12 _v5) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3 (@ite.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4)) (@Eq.{(0 + 1)} (@Bool) _v26 (@Bool.true)) (@instDecidableEqBool
  _v26 (@Bool.true)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v4) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject
  _v4)) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v21 _v20) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))
  _v19) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v25) (@NormalFinalClosure.Target.cleared _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v3 _v11 _v7)) _v22 _v23
  _v19))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @NormalClockClosure.bridge_full

-- Complete literal proposition for NormalClockClosure.bridge_full; original proof reused.
theorem PartACanonical.Surface.m0299 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (∀ (_v2 : (@Fin _v1)),
(@Bool))),
(let _v3 : (@Nat) := (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@HMul.hMul.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (1099511627776 : Nat)
  (@instOfNatNat (1099511627776 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))));
(let _v4 : (@Pnp3.Complexity.Uniform.V1.UniformTM) := (@NormalFinalClosure.machine2 _v0);
(let _v5 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v4 _v1 _v3 _v2);
(let _v6 : (@Pnp3.Complexity.Uniform.V1.UniformTM) := (@RawCallerClosure.machine _v0);
(let _v7 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v3) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v6 _v1 _v3 _v2);
(let _v8 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0))) :=
  (@RawCallerClosure.callerState _v0 (@PhysicalCallerClosure.rowsDone _v0));
(let _v9 : (∀ (_v9 : (@Bool)),
(@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0)))) := (fun (_v9 : (@Bool)) =>
(@RawCallerClosure.old _v0 (@CertificateGuardClosure.old _v0 (@TotalIngressClosure.old _v0 (@BodyIngress.old _v0
  (@CarryWindow.embed _v0 (@CanonicalLeaf.result _v0 _v9)))))));
(let _v10 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v1
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4503599627370496 : Nat) (@instOfNatNat
  (4503599627370496 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 :
  Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4503599627370496 : Nat) (@instOfNatNat
  (4503599627370496 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 :
  Nat)))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v11 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v12 : (@Nat)) =>
(@Exists.{0} (@LE.le.{0} (@Nat) (@instLENat) _v3 _v10) (fun (_v13 : (@LE.le.{0} (@Nat) (@instLENat) _v3 _v10)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v11 _v12) (@And (@LE.le.{0} (@Nat) (@instLENat) _v12 (@HMul.hMul.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (17592186044416 : Nat) (@instOfNatNat (17592186044416 : Nat))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat))))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 :
  Nat)))))) (@And (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v12 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v3) (@And (@LE.le.{0} (@Nat)
  (@instLENat) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (17592186044416 : Nat) (@instOfNatNat
  (17592186044416 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))))) _v10) (@And (∀ (_v14 : (@Nat)),
(∀ (_v15 : (@LE.le.{0} (@Nat) (@instLENat) _v14 _v12)),
(@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3
  _v14 _v5))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1
  _v3)))) (@And (∀ (_v14 : (@Nat)),
(∀ (_v15 : (@LE.le.{0} (@Nat) (@instLENat) _v3 _v14)),
(@And (∀ (_v16 : (@Nat)),
(∀ (_v17 : (@LE.le.{0} (@Nat) (@instLENat) _v16 _v12)),
(@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3 _v16 _v5)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v14 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v14
  _v16 (@Pnp3.Complexity.Uniform.V1.initialConfig _v4 _v1 _v14 _v2)))) (@And (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v14)) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v14 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v14
  _v16 (@Pnp3.Complexity.Uniform.V1.initialConfig _v4 _v1 _v14 _v2)))
  (@Pnp3.Complexity.Uniform.V1.FixedPairParser.tapeEmbed _v1 _v3 _v14 _v15 (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3
  _v16 _v5)))) (@And (∀ (_v18 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v14 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v14
  _v16 (@Pnp3.Complexity.Uniform.V1.initialConfig _v4 _v1 _v14 _v2))
  (@Pnp3.Complexity.Uniform.V1.FixedPairParser.tapeEmbed _v1 _v3 _v14 _v15 _v18)) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3
  _v16 _v5) _v18))) (@And (∀ (_v18 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v14))),
(∀ (_v19 : (@LE.le.{0} (@Nat) (@instLENat) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v14) _v18))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v14 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v14
  _v16 (@Pnp3.Complexity.Uniform.V1.initialConfig _v4 _v1 _v14 _v2)) _v18) (@Option.none.{0} (@Bool))))) (@And (@LE.le.{0}
  (@Nat) (@instLENat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3
  _v16 _v5))) _v12) (@LE.le.{0} (@Nat) (@instLENat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v14)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v14
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v14 _v16 (@Pnp3.Complexity.Uniform.V1.initialConfig _v4 _v1 _v14
  _v2)))) _v12)))))))) (@And (∀ (_v16 : (@Nat)),
(∀ (_v17 : (@LT.lt.{0} (@Nat) (@instLTNat) _v16 _v12)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v14
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v14 _v16 (@Pnp3.Complexity.Uniform.V1.initialConfig _v4 _v1 _v14
  _v2))) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v4)) (@And (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v14 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v14
  _v16 (@Pnp3.Complexity.Uniform.V1.initialConfig _v4 _v1 _v14 _v2))) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v4))
  (∀ (_v18 : (@Bool)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v14 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v14
  _v16 (@Pnp3.Complexity.Uniform.V1.initialConfig _v4 _v1 _v14 _v2))) (@NormalFinalClosure.old2 _v0 (@_v9 _v18)))))))) (∀
  (_v16 : (@Nat)),
(∀ (_v17 : (@LE.le.{0} (@Nat) (@instLENat) _v12 _v16)),
(∀ (_v18 : (@Or (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3 _v12 _v5)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v4))
  (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3
  _v12 _v5)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v4)))),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v14)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v14 _v16 (@Pnp3.Complexity.Uniform.V1.initialConfig _v4 _v1 _v14
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v14 _v12 (@Pnp3.Complexity.Uniform.V1.initialConfig _v4 _v1
  _v14 _v2)))))))))) (@And (∀ (_v14 : (@Bool)),
(∀ (_v15 : (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3 _v12 _v5)) (@ite.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4)) (@Eq.{(0 + 1)} (@Bool) _v14 (@Bool.true)) (@instDecidableEqBool
  _v14 (@Bool.true)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v4) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject
  _v4)))),
(@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1
  _v10) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v10 _v10 (@Pnp3.Complexity.Uniform.V1.initialConfig _v4 _v1
  _v10 _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v10 _v12 (@Pnp3.Complexity.Uniform.V1.initialConfig _v4
  _v1 _v10 _v2))) (@And (@Pnp3.Complexity.Uniform.V1.DecidesAt _v4 _v1 _v10 _v10 _v2 _v14)
  (@Pnp3.Complexity.Uniform.V1.DecidesWithin _v4 _v1 _v10 _v2 _v14))))) (@And (∀ (_v14 : (@Nat)),
(∀ (_v15 : (@LE.le.{0} (@Nat) (@instLENat) _v14 _v11)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3 _v14 _v5) (@NormalFinalClosure.config2 _v0 _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v3 _v14 _v7))))) (@And (∀ (_v14 : (@Nat)),
(∀ (_v15 : (@LE.le.{0} (@Nat) (@instLENat) _v14 _v11)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v3
  _v14 _v7)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v6)))) (@And (∀ (_v14 : (@Nat)),
(∀ (_v15 : (@LT.lt.{0} (@Nat) (@instLTNat) _v14 _v11)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v3 _v14 _v7)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v6))
  (@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v3 _v14 _v7)) _v8) (∀ (_v16 : (@Bool)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v3
  _v14 _v7)) (@_v9 _v16))))))) (@And (∀ (_v14 : (@Nat)),
(∀ (_v15 : (@LT.lt.{0} (@Nat) (@instLTNat) _v14 _v12)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3 _v14 _v5)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v4))
  (@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3 _v14 _v5)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v4)) (∀
  (_v16 : (@Bool)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3
  _v14 _v5)) (@NormalFinalClosure.old2 _v0 (@_v9 _v16)))))))) (@Or (@And (@Eq.{(0 + 1)} (@Nat) _v12 _v11) (@And
  (@Exists.{(0 + 1)} (@Bool) (fun (_v14 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v3
  _v11 _v7)) (@_v9 _v14)))) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3
  _v12 _v5) (@NormalFinalClosure.config2 _v0 _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v3 _v11 _v7)))))
  (@Or (@And (@Eq.{(0 + 1)} (@Nat) _v12 _v11) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  _v6)) (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v3 _v11 _v7)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v6))
  (@And (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.encodedRelationLanguage
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0) _v1 _v2) (@Bool.false)) (@Eq.{(0 +
  1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3 _v12 _v5) (@NormalFinalClosure.config2 _v0 _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v3 _v11 _v7)))))) (@Exists.{(0 + 1)} (@Nat) (fun (_v14 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v15 : (@Nat)) =>
(@Exists.{(0 + 1)} (∀ (_v16 : (@Fin _v14)),
(@Bool)) (fun (_v16 : (∀ (_v16 : (@Fin _v14)),
(@Bool))) =>
(@Exists.{(0 + 1)} (∀ (_v17 : (@Fin _v15)),
(@Bool)) (fun (_v17 : (∀ (_v17 : (@Fin _v15)),
(@Bool))) =>
(@Exists.{0} (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v14 _v15) _v1) (fun (_v18 :
  (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v14 _v15) _v1)) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.decodePair _v1 _v2) (@Option.some.{0} (@Prod.{0, 0} (@Sigma.{0, 0} (@Nat) (fun
  (_v19 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v19))) (@Sigma.{0, 0} (@Nat) (fun (_v19 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v19)))) (@Prod.mk.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v19 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v19))) (@Sigma.{0, 0} (@Nat) (fun (_v19 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v19))) (@Sigma.mk.{0, 0} (@Nat) (fun (_v19 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v19)) _v14 _v16) (@Sigma.mk.{0, 0} (@Nat) (fun (_v19 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v19)) _v15 _v17)))) (@And (@Eq.{(0 + 1)} (∀ (_v19 : (@Fin _v1)),
(@Bool)) _v2 (@Eq.rec.{(0 + 1), (0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v14 _v15) (fun
  (_v19 : (@Nat)) =>
(fun (_v20 : (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v14 _v15) _v19)) =>
(∀ (_v21 : (@Fin _v19)),
(@Bool)))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v14 _v15 _v16 _v17) _v1 _v18)) (@And (@Eq.{(0 + 1)}
  (@Nat) _v15 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Exists.{(0 + 1)} (@Nat) (fun (_v19 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v20 : (@Nat)) =>
(@And (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.tagMatches (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 _v15) (@Fin.append.{(0 + 1)} _v14 _v15 (@Bool) _v16 _v17))
  (@Bool.true)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Nat))
  (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros? (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 _v15) (@Fin.append.{(0 + 1)} _v14 _v15 (@Bool) _v16 _v17)) (@Option.some.{0}
  (@Nat) _v20)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Nat) (@Nat)))
  (@Pnp4.Frontier.ContractExpansion.contentHeader? (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v14 _v15) (@Fin.append.{(0 + 1)} _v14 _v15 (@Bool) _v16 _v17)) (@Option.some.{0} (@Prod.{0, 0} (@Nat)
  (@Nat)) (@Prod.mk.{0, 0} (@Nat) (@Nat) _v19 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v20) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))) (let _v21 :
  (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 _v15);
(let _v22 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v1);
(let _v23 : (@Nat) := (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v21 (@Min.min.{0}
  (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v20)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v19)) _v21));
(let _v24 : (@Nat) := (@Cursor.Target.W _v0 _v19);
(@And (@LT.lt.{0} (@Nat) (@instLTNat) (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v20))
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v19)) _v21) _v21) (@And (@LE.le.{0}
  (@Nat) (@instLENat) (@Pnp4.Frontier.ContractExpansion.bitLength _v19) _v23) (@And (@LE.le.{0} (@Nat) (@instLENat) _v24
  _v23) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v3 _v11 _v7)) _v8) (@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v21 _v20)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v19) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3)) (fun (_v25 : (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v21 _v20)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v19) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3))) =>
(@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3)) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v3
  _v11 _v7)) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v21 _v20) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))
  _v19) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v25)) (@Exists.{(0 + 1)} (@Bool) (fun (_v26 :
  (@Bool)) =>
(@And (@Eq.{(0 + 1)} (@Bool) _v26 (@Pnp3.Complexity.Uniform.V1.encodedRelationLanguage
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0) _v1 _v2)) (@And (@Eq.{(0 + 1)}
  (@Bool) _v26 (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v14 _v15 _v16 _v17))
  (@And (@Iff (@Eq.{(0 + 1)} (@Bool) _v26 (@Bool.true)) (@Exists.{(0 + 1)} (@Nat) (fun (_v27 : (@Nat)) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@Pnp4.Frontier.ContractExpansion.readNatBE (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v20)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v19))
  (@Pnp4.Frontier.ContractExpansion.bitLength _v24)) _v24) (@Pnp4.Frontier.ContractExpansion.padWord (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 _v15) (@Fin.append.{(0 + 1)} _v14 _v15 (@Bool) _v16 _v17)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat)
  (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v20)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v19)) (@Pnp4.Frontier.ContractExpansion.bitLength _v24)) _v24)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v20))
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v19))
  (@Pnp4.Frontier.ContractExpansion.bitLength _v24)) (@Option.some.{0} (@Nat) _v27)) (@And (@LE.le.{0} (@Nat) (@instLENat)
  _v27 _v24) (@And (∀ (_v28 : (@Nat)),
(∀ (_v29 : (@LT.lt.{0} (@Nat) (@instLTNat) _v28 _v27)),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 _v15) (@Fin.append.{(0 + 1)} _v14 _v15 (@Bool) _v16 _v17) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 :
  Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))) _v20)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v19))
  (@Pnp4.Frontier.ContractExpansion.bitLength _v24)) _v28)) (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 _v15) (@Fin.append.{(0 + 1)} _v14 _v15 (@Bool) _v16
  _v17) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v20)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v19))
  (@Pnp4.Frontier.ContractExpansion.bitLength _v24)) _v24) _v28))))) (∀ (_v28 : (@Nat)),
(∀ (_v29 : (@LE.le.{0} (@Nat) (@instLENat) _v27 _v28)),
(∀ (_v30 : (@LT.lt.{0} (@Nat) (@instLTNat) _v28 _v24)),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 _v15) (@Fin.append.{(0 + 1)} _v14 _v15 (@Bool) _v16 _v17) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 :
  Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))) _v20)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v19))
  (@Pnp4.Frontier.ContractExpansion.bitLength _v24)) _v28)) (@Bool.false))))))))))) (@Eq.{(0 + 1)}
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3 _v12 _v5) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3 (@ite.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4)) (@Eq.{(0 + 1)} (@Bool) _v26 (@Bool.true)) (@instDecidableEqBool
  _v26 (@Bool.true)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v4) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject
  _v4)) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v21 _v20) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))
  _v19) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v25) (@NormalFinalClosure.Target.cleared _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v6) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v6 _v1 _v3 _v11 _v7)) _v22 _v23
  _v19))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @NormalClockClosure.bridge_full

-- Independent literal expected type for NormalClockClosure.clock_bound.
noncomputable def PartACanonical.Types.p0514 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(@And (@LE.le.{0} (@Nat) (@instLENat) (@RawCallerClosure.allocation _v0 _v1) (@Pnp3.Complexity.Uniform.V1.polyClock
  (@NormalClockClosure.degree _v0) _v1)) (@LE.le.{0} (@Nat) (@instLENat) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (17592186044416 : Nat) (@instOfNatNat (17592186044416 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 :
  Nat))))) (@Pnp3.Complexity.Uniform.V1.polyClock (@NormalClockClosure.degree _v0) _v1))))) := by
  exact @NormalClockClosure.clock_bound

-- Complete literal proposition for NormalClockClosure.clock_bound; original proof reused.
theorem PartACanonical.Surface.m0300 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(@And (@LE.le.{0} (@Nat) (@instLENat) (@RawCallerClosure.allocation _v0 _v1) (@Pnp3.Complexity.Uniform.V1.polyClock
  (@NormalClockClosure.degree _v0) _v1)) (@LE.le.{0} (@Nat) (@instLENat) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (17592186044416 : Nat) (@instOfNatNat (17592186044416 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 :
  Nat))))) (@Pnp3.Complexity.Uniform.V1.polyClock (@NormalClockClosure.degree _v0) _v1))))) := by
  exact @NormalClockClosure.clock_bound

-- Independent literal expected type for NormalClockClosure.clock_bound_mirror.
noncomputable def PartACanonical.Types.p0515 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(@And (@LE.le.{0} (@Nat) (@instLENat) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (1099511627776
  : Nat) (@instOfNatNat (1099511627776 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (4503599627370496 : Nat) (@instOfNatNat (4503599627370496 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))
  (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (4503599627370496 : Nat) (@instOfNatNat (4503599627370496 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))
  (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))))) (@LE.le.{0} (@Nat) (@instLENat) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (17592186044416 : Nat) (@instOfNatNat (17592186044416 : Nat)))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat)
  (@instOfNatNat (8 : Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) _v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4503599627370496 : Nat)
  (@instOfNatNat (4503599627370496 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (64 : Nat)
  (@instOfNatNat (64 : Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (4503599627370496 : Nat) (@instOfNatNat (4503599627370496 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))
  (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))))))))) := by
  exact @NormalClockClosure.clock_bound_mirror

-- Complete literal proposition for NormalClockClosure.clock_bound_mirror; original proof reused.
theorem PartACanonical.Surface.m0301 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(@And (@LE.le.{0} (@Nat) (@instLENat) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (1099511627776
  : Nat) (@instOfNatNat (1099511627776 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (4503599627370496 : Nat) (@instOfNatNat (4503599627370496 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))
  (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (4503599627370496 : Nat) (@instOfNatNat (4503599627370496 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))
  (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))))) (@LE.le.{0} (@Nat) (@instLENat) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (17592186044416 : Nat) (@instOfNatNat (17592186044416 : Nat)))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat)
  (@instOfNatNat (8 : Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) _v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4503599627370496 : Nat)
  (@instOfNatNat (4503599627370496 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (64 : Nat)
  (@instOfNatNat (64 : Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (4503599627370496 : Nat) (@instOfNatNat (4503599627370496 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))
  (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))))))))) := by
  exact @NormalClockClosure.clock_bound_mirror

-- Independent literal expected type for NormalClockClosure.degree.
noncomputable def PartACanonical.Types.p0516 :
(∀ (_v0 : (@Nat)),
(@Nat)) := by
  exact @NormalClockClosure.degree

-- Independent literal expected type for NormalFinalClosure.Target.PrefixOK.
noncomputable def PartACanonical.Types.p0517 :
(∀ {_v0 : (@Nat)},
(∀ (_v1 : (∀ (_v1 : (@Fin _v0)),
(@Bool))),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(Sort 0)))))) := by
  exact @NormalFinalClosure.Target.PrefixOK

-- Independent literal expected type for NormalFinalClosure.Target.Raw.
noncomputable def PartACanonical.Types.p0518 :
(∀ (_v0 : (@Nat)),
(Sort 0)) := by
  exact @NormalFinalClosure.Target.Raw

-- Independent literal expected type for NormalFinalClosure.Target.cleared.
noncomputable def PartACanonical.Types.p0519 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ (_v2 : (∀ (_v2 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))),
(@Option.{0} (@Bool)))),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))),
(@Option.{0} (@Bool))))))))) := by
  exact @NormalFinalClosure.Target.cleared

-- Independent literal expected type for NormalFinalClosure.Target.cleared.eq_1.
noncomputable def PartACanonical.Types.p0520 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ (_v2 : (∀ (_v2 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))),
(@Option.{0} (@Bool)))),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@NormalFinalClosure.Target.cleared _v0 _v1 _v2 _v3 _v4 _v5 _v6) (@ite.{(0 + 1)}
  (@Option.{0} (@Bool)) (@Or (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter _v3 _v4 _v5
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0
  _v1) _v6)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6)
  (@SerializedBody.delimiter _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))) (@Or (@And
  (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat
  (5 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6) (@SerializedBody.delimiter _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (6
  : Nat) (@instOfNatNat (6 : Nat)))))) (@Or (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter _v3 _v4 _v5
  (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0
  _v1) _v6)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6)
  (@SerializedBody.delimiter _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))))) (@And
  (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6)) (@LT.lt.{0} (@Nat)
  (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6) (@SerializedBody.delimiter _v3 _v4 _v5
  (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))))))) (@instDecidableOr (@And (@LT.lt.{0} (@Nat)
  (@instLTNat) (@SerializedBody.delimiter _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6) (@SerializedBody.delimiter _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (5
  : Nat) (@instOfNatNat (5 : Nat)))))) (@Or (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter _v3 _v4 _v5
  (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0
  _v1) _v6)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6)
  (@SerializedBody.delimiter _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))) (@Or (@And
  (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat
  (6 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6) (@SerializedBody.delimiter _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (7
  : Nat) (@instOfNatNat (7 : Nat)))))) (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter _v3 _v4 _v5
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0
  _v1) _v6)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6)
  (@SerializedBody.delimiter _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))))))
  (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6)) (@LT.lt.{0} (@Nat)
  (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6) (@SerializedBody.delimiter _v3 _v4 _v5
  (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))) (@Nat.decLt (@SerializedBody.delimiter _v3 _v4 _v5
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0
  _v1) _v6)) (@Nat.decLt (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6) (@SerializedBody.delimiter _v3
  _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))) (@instDecidableOr (@And (@LT.lt.{0} (@Nat)
  (@instLTNat) (@SerializedBody.delimiter _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6) (@SerializedBody.delimiter _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (6
  : Nat) (@instOfNatNat (6 : Nat)))))) (@Or (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter _v3 _v4 _v5
  (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0
  _v1) _v6)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6)
  (@SerializedBody.delimiter _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))))) (@And
  (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6)) (@LT.lt.{0} (@Nat)
  (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6) (@SerializedBody.delimiter _v3 _v4 _v5
  (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat)
  (@SerializedBody.delimiter _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6) (@SerializedBody.delimiter _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (6
  : Nat) (@instOfNatNat (6 : Nat))))) (@Nat.decLt (@SerializedBody.delimiter _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (5 :
  Nat) (@instOfNatNat (5 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6)) (@Nat.decLt (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6) (@SerializedBody.delimiter _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (6
  : Nat) (@instOfNatNat (6 : Nat)))))) (@instDecidableOr (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter
  _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6) (@SerializedBody.delimiter _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (7
  : Nat) (@instOfNatNat (7 : Nat)))))) (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter _v3 _v4 _v5
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0
  _v1) _v6)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6)
  (@SerializedBody.delimiter _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))))
  (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (6 :
  Nat) (@instOfNatNat (6 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6)) (@LT.lt.{0} (@Nat)
  (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6) (@SerializedBody.delimiter _v3 _v4 _v5
  (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))) (@Nat.decLt (@SerializedBody.delimiter _v3 _v4 _v5
  (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0
  _v1) _v6)) (@Nat.decLt (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6) (@SerializedBody.delimiter _v3
  _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))))) (@instDecidableAnd (@LT.lt.{0} (@Nat)
  (@instLTNat) (@SerializedBody.delimiter _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6) (@SerializedBody.delimiter _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat)
  (12 : Nat) (@instOfNatNat (12 : Nat))))) (@Nat.decLt (@SerializedBody.delimiter _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (11
  : Nat) (@instOfNatNat (11 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6)) (@Nat.decLt
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6) (@SerializedBody.delimiter _v3 _v4 _v5 (@OfNat.ofNat.{0}
  (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))))))) (@Option.some.{0} (@Bool) (@Bool.false)) (@ite.{(0 + 1)}
  (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter _v3 _v4 _v5 (@OfNat.ofNat.{0}
  (@Nat) (10 : Nat) (@instOfNatNat (10 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6))
  (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6)
  (@SerializedBody.delimiter _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))))
  (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (10 :
  Nat) (@instOfNatNat (10 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6)) (@LT.lt.{0} (@Nat)
  (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6) (@SerializedBody.delimiter _v3 _v4 _v5
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))) (@Nat.decLt (@SerializedBody.delimiter _v3 _v4 _v5
  (@OfNat.ofNat.{0} (@Nat) (10 : Nat) (@instOfNatNat (10 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0
  _v1) _v6)) (@Nat.decLt (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6) (@SerializedBody.delimiter _v3
  _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))))) (@Option.some.{0} (@Bool) (@Bool.true)) (@_v2
  _v6))))))))))) := by
  exact @NormalFinalClosure.Target.cleared.eq_1

-- Complete literal proposition for NormalFinalClosure.Target.cleared.eq_1; original proof reused.
theorem PartACanonical.Surface.m0302 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ (_v2 : (∀ (_v2 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))),
(@Option.{0} (@Bool)))),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@NormalFinalClosure.Target.cleared _v0 _v1 _v2 _v3 _v4 _v5 _v6) (@ite.{(0 + 1)}
  (@Option.{0} (@Bool)) (@Or (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter _v3 _v4 _v5
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0
  _v1) _v6)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6)
  (@SerializedBody.delimiter _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))) (@Or (@And
  (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat
  (5 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6) (@SerializedBody.delimiter _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (6
  : Nat) (@instOfNatNat (6 : Nat)))))) (@Or (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter _v3 _v4 _v5
  (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0
  _v1) _v6)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6)
  (@SerializedBody.delimiter _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))))) (@And
  (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6)) (@LT.lt.{0} (@Nat)
  (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6) (@SerializedBody.delimiter _v3 _v4 _v5
  (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))))))) (@instDecidableOr (@And (@LT.lt.{0} (@Nat)
  (@instLTNat) (@SerializedBody.delimiter _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6) (@SerializedBody.delimiter _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (5
  : Nat) (@instOfNatNat (5 : Nat)))))) (@Or (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter _v3 _v4 _v5
  (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0
  _v1) _v6)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6)
  (@SerializedBody.delimiter _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))) (@Or (@And
  (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat
  (6 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6) (@SerializedBody.delimiter _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (7
  : Nat) (@instOfNatNat (7 : Nat)))))) (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter _v3 _v4 _v5
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0
  _v1) _v6)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6)
  (@SerializedBody.delimiter _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))))))
  (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6)) (@LT.lt.{0} (@Nat)
  (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6) (@SerializedBody.delimiter _v3 _v4 _v5
  (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))) (@Nat.decLt (@SerializedBody.delimiter _v3 _v4 _v5
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0
  _v1) _v6)) (@Nat.decLt (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6) (@SerializedBody.delimiter _v3
  _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))) (@instDecidableOr (@And (@LT.lt.{0} (@Nat)
  (@instLTNat) (@SerializedBody.delimiter _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6) (@SerializedBody.delimiter _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (6
  : Nat) (@instOfNatNat (6 : Nat)))))) (@Or (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter _v3 _v4 _v5
  (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0
  _v1) _v6)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6)
  (@SerializedBody.delimiter _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))))) (@And
  (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6)) (@LT.lt.{0} (@Nat)
  (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6) (@SerializedBody.delimiter _v3 _v4 _v5
  (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat)
  (@SerializedBody.delimiter _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6) (@SerializedBody.delimiter _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (6
  : Nat) (@instOfNatNat (6 : Nat))))) (@Nat.decLt (@SerializedBody.delimiter _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (5 :
  Nat) (@instOfNatNat (5 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6)) (@Nat.decLt (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6) (@SerializedBody.delimiter _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (6
  : Nat) (@instOfNatNat (6 : Nat)))))) (@instDecidableOr (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter
  _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6) (@SerializedBody.delimiter _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (7
  : Nat) (@instOfNatNat (7 : Nat)))))) (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter _v3 _v4 _v5
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0
  _v1) _v6)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6)
  (@SerializedBody.delimiter _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))))
  (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (6 :
  Nat) (@instOfNatNat (6 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6)) (@LT.lt.{0} (@Nat)
  (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6) (@SerializedBody.delimiter _v3 _v4 _v5
  (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))) (@Nat.decLt (@SerializedBody.delimiter _v3 _v4 _v5
  (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0
  _v1) _v6)) (@Nat.decLt (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6) (@SerializedBody.delimiter _v3
  _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))))) (@instDecidableAnd (@LT.lt.{0} (@Nat)
  (@instLTNat) (@SerializedBody.delimiter _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6)) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6) (@SerializedBody.delimiter _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat)
  (12 : Nat) (@instOfNatNat (12 : Nat))))) (@Nat.decLt (@SerializedBody.delimiter _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (11
  : Nat) (@instOfNatNat (11 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6)) (@Nat.decLt
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6) (@SerializedBody.delimiter _v3 _v4 _v5 (@OfNat.ofNat.{0}
  (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))))))) (@Option.some.{0} (@Bool) (@Bool.false)) (@ite.{(0 + 1)}
  (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter _v3 _v4 _v5 (@OfNat.ofNat.{0}
  (@Nat) (10 : Nat) (@instOfNatNat (10 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6))
  (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6)
  (@SerializedBody.delimiter _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))))
  (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (10 :
  Nat) (@instOfNatNat (10 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6)) (@LT.lt.{0} (@Nat)
  (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6) (@SerializedBody.delimiter _v3 _v4 _v5
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))) (@Nat.decLt (@SerializedBody.delimiter _v3 _v4 _v5
  (@OfNat.ofNat.{0} (@Nat) (10 : Nat) (@instOfNatNat (10 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0
  _v1) _v6)) (@Nat.decLt (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v6) (@SerializedBody.delimiter _v3
  _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))))) (@Option.some.{0} (@Bool) (@Bool.true)) (@_v2
  _v6))))))))))) := by
  exact @NormalFinalClosure.Target.cleared.eq_1

-- Independent literal expected type for NormalFinalClosure.Target2.Raw.
noncomputable def PartACanonical.Types.p0521 :
(∀ (_v0 : (@Nat)),
(Sort 0)) := by
  exact @NormalFinalClosure.Target2.Raw

-- Independent literal expected type for NormalFinalClosure.accepted_content_rows.
noncomputable def PartACanonical.Types.p0522 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ {_v3 : (@Nat)},
(∀ (_v4 : (∀ (_v4 : (@Fin _v3)),
(@Bool))),
(∀ (_v5 : (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Nat) (@Nat))) (@Pnp4.Frontier.ContractExpansion.contentHeader? _v3
  _v4) (@Option.some.{0} (@Prod.{0, 0} (@Nat) (@Nat)) (@Prod.mk.{0, 0} (@Nat) (@Nat) _v1 (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v2) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))))))),
(∀ (_v6 : (@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.contentSemanticAccepts
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v3 _v4) (@Bool.true))),
(@Exists.{(0 + 1)} (@Pnp3.Models.Circuit _v1) (fun (_v7 : (@Pnp3.Models.Circuit _v1)) =>
(@Exists.{(0 + 1)} (@List.{0} (@Bool)) (fun (_v8 : (@List.{0} (@Bool))) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Pnp3.Models.Circuit _v1) (@List.{0} (@Bool))))
  (@Pnp4.Frontier.ContractExpansion.decodeCircuitFull _v1 (@Pnp4.Frontier.ContractExpansion.bitLength _v1)
  (@SerializedBody.window _v3 _v4 (@Cursor.Target.M _v0 _v1 _v2) (@Cursor.Target.W _v0 _v1))) (@Option.some.{0} (@Prod.{0,
  0} (@Pnp3.Models.Circuit _v1) (@List.{0} (@Bool))) (@Prod.mk.{0, 0} (@Pnp3.Models.Circuit _v1) (@List.{0} (@Bool)) _v7
  _v8))) (@And (@LE.le.{0} (@Nat) (@instLENat) (@Pnp3.Models.Circuit.size _v1 _v7) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v1 _v0) _v0)) (∀ (_v9 : (@Nat)),
(∀ (_v10 : (@LT.lt.{0} (@Nat) (@instLTNat) _v9 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat)
  (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v1))),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead _v3 _v4 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v2)) _v9))
  (@Pnp3.Models.Circuit.eval _v1 _v7 (@Pnp3.Core.vecOfNat _v1 _v9)))))))))))))))))) := by
  exact @NormalFinalClosure.accepted_content_rows

-- Complete literal proposition for NormalFinalClosure.accepted_content_rows; original proof reused.
theorem PartACanonical.Surface.m0303 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ {_v3 : (@Nat)},
(∀ (_v4 : (∀ (_v4 : (@Fin _v3)),
(@Bool))),
(∀ (_v5 : (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Nat) (@Nat))) (@Pnp4.Frontier.ContractExpansion.contentHeader? _v3
  _v4) (@Option.some.{0} (@Prod.{0, 0} (@Nat) (@Nat)) (@Prod.mk.{0, 0} (@Nat) (@Nat) _v1 (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v2) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))))))),
(∀ (_v6 : (@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.contentSemanticAccepts
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v3 _v4) (@Bool.true))),
(@Exists.{(0 + 1)} (@Pnp3.Models.Circuit _v1) (fun (_v7 : (@Pnp3.Models.Circuit _v1)) =>
(@Exists.{(0 + 1)} (@List.{0} (@Bool)) (fun (_v8 : (@List.{0} (@Bool))) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Pnp3.Models.Circuit _v1) (@List.{0} (@Bool))))
  (@Pnp4.Frontier.ContractExpansion.decodeCircuitFull _v1 (@Pnp4.Frontier.ContractExpansion.bitLength _v1)
  (@SerializedBody.window _v3 _v4 (@Cursor.Target.M _v0 _v1 _v2) (@Cursor.Target.W _v0 _v1))) (@Option.some.{0} (@Prod.{0,
  0} (@Pnp3.Models.Circuit _v1) (@List.{0} (@Bool))) (@Prod.mk.{0, 0} (@Pnp3.Models.Circuit _v1) (@List.{0} (@Bool)) _v7
  _v8))) (@And (@LE.le.{0} (@Nat) (@instLENat) (@Pnp3.Models.Circuit.size _v1 _v7) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v1 _v0) _v0)) (∀ (_v9 : (@Nat)),
(∀ (_v10 : (@LT.lt.{0} (@Nat) (@instLTNat) _v9 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat)
  (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v1))),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead _v3 _v4 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v2)) _v9))
  (@Pnp3.Models.Circuit.eval _v1 _v7 (@Pnp3.Core.vecOfNat _v1 _v9)))))))))))))))))) := by
  exact @NormalFinalClosure.accepted_content_rows

-- Independent literal expected type for NormalFinalClosure.accepted_content_rows_mirror.
noncomputable def PartACanonical.Types.p0523 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ {_v3 : (@Nat)},
(∀ (_v4 : (∀ (_v4 : (@Fin _v3)),
(@Bool))),
(∀ (_v5 : (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Nat) (@Nat))) (@Pnp4.Frontier.ContractExpansion.contentHeader? _v3
  _v4) (@Option.some.{0} (@Prod.{0, 0} (@Nat) (@Nat)) (@Prod.mk.{0, 0} (@Nat) (@Nat) _v1 (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v2) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))))))),
(∀ (_v6 : (@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.contentSemanticAccepts
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v3 _v4) (@Bool.true))),
(@Exists.{(0 + 1)} (@Pnp3.Models.Circuit _v1) (fun (_v7 : (@Pnp3.Models.Circuit _v1)) =>
(@Exists.{(0 + 1)} (@List.{0} (@Bool)) (fun (_v8 : (@List.{0} (@Bool))) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Pnp3.Models.Circuit _v1) (@List.{0} (@Bool))))
  (@Pnp4.Frontier.ContractExpansion.decodeCircuitFull _v1 (@Pnp4.Frontier.ContractExpansion.bitLength _v1)
  (@SerializedBody.window _v3 _v4 (@Cursor.Target.M _v0 _v1 _v2) (@Cursor.Target.W _v0 _v1))) (@Option.some.{0} (@Prod.{0,
  0} (@Pnp3.Models.Circuit _v1) (@List.{0} (@Bool))) (@Prod.mk.{0, 0} (@Pnp3.Models.Circuit _v1) (@List.{0} (@Bool)) _v7
  _v8))) (@And (@LE.le.{0} (@Nat) (@instLENat) (@Pnp3.Models.Circuit.size _v1 _v7) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v1 _v0) _v0)) (∀ (_v9 : (@Nat)),
(∀ (_v10 : (@LT.lt.{0} (@Nat) (@instLTNat) _v9 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat)
  (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v1))),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead _v3 _v4 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v2)) _v9))
  (@Pnp3.Models.Circuit.eval _v1 _v7 (@Pnp3.Core.vecOfNat _v1 _v9)))))))))))))))))) := by
  exact @NormalFinalClosure.accepted_content_rows_mirror

-- Complete literal proposition for NormalFinalClosure.accepted_content_rows_mirror; original proof reused.
theorem PartACanonical.Surface.m0304 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ {_v3 : (@Nat)},
(∀ (_v4 : (∀ (_v4 : (@Fin _v3)),
(@Bool))),
(∀ (_v5 : (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Nat) (@Nat))) (@Pnp4.Frontier.ContractExpansion.contentHeader? _v3
  _v4) (@Option.some.{0} (@Prod.{0, 0} (@Nat) (@Nat)) (@Prod.mk.{0, 0} (@Nat) (@Nat) _v1 (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v2) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))))))),
(∀ (_v6 : (@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.contentSemanticAccepts
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v3 _v4) (@Bool.true))),
(@Exists.{(0 + 1)} (@Pnp3.Models.Circuit _v1) (fun (_v7 : (@Pnp3.Models.Circuit _v1)) =>
(@Exists.{(0 + 1)} (@List.{0} (@Bool)) (fun (_v8 : (@List.{0} (@Bool))) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Pnp3.Models.Circuit _v1) (@List.{0} (@Bool))))
  (@Pnp4.Frontier.ContractExpansion.decodeCircuitFull _v1 (@Pnp4.Frontier.ContractExpansion.bitLength _v1)
  (@SerializedBody.window _v3 _v4 (@Cursor.Target.M _v0 _v1 _v2) (@Cursor.Target.W _v0 _v1))) (@Option.some.{0} (@Prod.{0,
  0} (@Pnp3.Models.Circuit _v1) (@List.{0} (@Bool))) (@Prod.mk.{0, 0} (@Pnp3.Models.Circuit _v1) (@List.{0} (@Bool)) _v7
  _v8))) (@And (@LE.le.{0} (@Nat) (@instLENat) (@Pnp3.Models.Circuit.size _v1 _v7) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v1 _v0) _v0)) (∀ (_v9 : (@Nat)),
(∀ (_v10 : (@LT.lt.{0} (@Nat) (@instLTNat) _v9 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat)
  (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v1))),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead _v3 _v4 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v2)) _v9))
  (@Pnp3.Models.Circuit.eval _v1 _v7 (@Pnp3.Core.vecOfNat _v1 _v9)))))))))))))))))) := by
  exact @NormalFinalClosure.accepted_content_rows_mirror

-- Independent literal expected type for NormalFinalClosure.codec_rows.
noncomputable def PartACanonical.Types.p0524 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Nat))),
(∀ {_v1 : (@Nat)},
(∀ (_v2 : (∀ (_v2 : (@Fin _v1)),
(@Bool))),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (∀ (_v5 : (@Fin (@Pnp4.Frontier.TreeCircuitWitnessCodec.witnessBits _v0
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec _v0) _v4))),
(@Bool))),
(@Iff (@Pnp4.Frontier.TreeCircuitWitnessCodec.verifies _v0 (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  _v0) _v4 (fun (_v6 : (@Fin (@Pnp3.Models.Partial.tableLen _v4))) =>
(@Pnp4.Frontier.ContractExpansion.padRead _v1 _v2 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 (@Fin.val (@Pnp3.Models.Partial.tableLen _v4) _v6)))) _v5) (@Exists.{(0 + 1)} (@Pnp3.Models.Circuit
  _v4) (fun (_v6 : (@Pnp3.Models.Circuit _v4)) =>
(@Exists.{(0 + 1)} (@List.{0} (@Bool)) (fun (_v7 : (@List.{0} (@Bool))) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Pnp3.Models.Circuit _v4) (@List.{0} (@Bool))))
  (@Pnp4.Frontier.ContractExpansion.decodeCircuitFull _v4 (@Pnp4.Frontier.ContractExpansion.bitLength _v4) (@List.ofFn.{0}
  (@Bool) (@Pnp4.Frontier.TreeCircuitWitnessCodec.witnessBits _v0
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec _v0) _v4) _v5)) (@Option.some.{0} (@Prod.{0, 0}
  (@Pnp3.Models.Circuit _v4) (@List.{0} (@Bool))) (@Prod.mk.{0, 0} (@Pnp3.Models.Circuit _v4) (@List.{0} (@Bool)) _v6
  _v7))) (@And (@LE.le.{0} (@Nat) (@instLENat) (@Pnp3.Models.Circuit.size _v4 _v6) (@_v0 _v4)) (∀ (_v8 : (@Nat)),
(∀ (_v9 : (@LT.lt.{0} (@Nat) (@instLTNat) _v8 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4))),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead _v1 _v2 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v8)) (@Pnp3.Models.Circuit.eval _v4 _v6 (@Pnp3.Core.vecOfNat _v4
  _v8)))))))))))))))))) := by
  exact @NormalFinalClosure.codec_rows

-- Complete literal proposition for NormalFinalClosure.codec_rows; original proof reused.
theorem PartACanonical.Surface.m0305 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Nat))),
(∀ {_v1 : (@Nat)},
(∀ (_v2 : (∀ (_v2 : (@Fin _v1)),
(@Bool))),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (∀ (_v5 : (@Fin (@Pnp4.Frontier.TreeCircuitWitnessCodec.witnessBits _v0
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec _v0) _v4))),
(@Bool))),
(@Iff (@Pnp4.Frontier.TreeCircuitWitnessCodec.verifies _v0 (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  _v0) _v4 (fun (_v6 : (@Fin (@Pnp3.Models.Partial.tableLen _v4))) =>
(@Pnp4.Frontier.ContractExpansion.padRead _v1 _v2 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 (@Fin.val (@Pnp3.Models.Partial.tableLen _v4) _v6)))) _v5) (@Exists.{(0 + 1)} (@Pnp3.Models.Circuit
  _v4) (fun (_v6 : (@Pnp3.Models.Circuit _v4)) =>
(@Exists.{(0 + 1)} (@List.{0} (@Bool)) (fun (_v7 : (@List.{0} (@Bool))) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Pnp3.Models.Circuit _v4) (@List.{0} (@Bool))))
  (@Pnp4.Frontier.ContractExpansion.decodeCircuitFull _v4 (@Pnp4.Frontier.ContractExpansion.bitLength _v4) (@List.ofFn.{0}
  (@Bool) (@Pnp4.Frontier.TreeCircuitWitnessCodec.witnessBits _v0
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec _v0) _v4) _v5)) (@Option.some.{0} (@Prod.{0, 0}
  (@Pnp3.Models.Circuit _v4) (@List.{0} (@Bool))) (@Prod.mk.{0, 0} (@Pnp3.Models.Circuit _v4) (@List.{0} (@Bool)) _v6
  _v7))) (@And (@LE.le.{0} (@Nat) (@instLENat) (@Pnp3.Models.Circuit.size _v4 _v6) (@_v0 _v4)) (∀ (_v8 : (@Nat)),
(∀ (_v9 : (@LT.lt.{0} (@Nat) (@instLTNat) _v8 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4))),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead _v1 _v2 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v8)) (@Pnp3.Models.Circuit.eval _v4 _v6 (@Pnp3.Core.vecOfNat _v4
  _v8)))))))))))))))))) := by
  exact @NormalFinalClosure.codec_rows

-- Independent literal expected type for NormalFinalClosure.codec_rows_mirror.
noncomputable def PartACanonical.Types.p0525 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Nat))),
(∀ {_v1 : (@Nat)},
(∀ (_v2 : (∀ (_v2 : (@Fin _v1)),
(@Bool))),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (∀ (_v5 : (@Fin (@Pnp4.Frontier.TreeCircuitWitnessCodec.witnessBits _v0
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec _v0) _v4))),
(@Bool))),
(@Iff (@Pnp4.Frontier.TreeCircuitWitnessCodec.verifies _v0 (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  _v0) _v4 (fun (_v6 : (@Fin (@Pnp3.Models.Partial.tableLen _v4))) =>
(@Pnp4.Frontier.ContractExpansion.padRead _v1 _v2 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 (@Fin.val (@Pnp3.Models.Partial.tableLen _v4) _v6)))) _v5) (@Exists.{(0 + 1)} (@Pnp3.Models.Circuit
  _v4) (fun (_v6 : (@Pnp3.Models.Circuit _v4)) =>
(@Exists.{(0 + 1)} (@List.{0} (@Bool)) (fun (_v7 : (@List.{0} (@Bool))) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Pnp3.Models.Circuit _v4) (@List.{0} (@Bool))))
  (@Pnp4.Frontier.ContractExpansion.decodeCircuitFull _v4 (@Pnp4.Frontier.ContractExpansion.bitLength _v4) (@List.ofFn.{0}
  (@Bool) (@Pnp4.Frontier.TreeCircuitWitnessCodec.witnessBits _v0
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec _v0) _v4) _v5)) (@Option.some.{0} (@Prod.{0, 0}
  (@Pnp3.Models.Circuit _v4) (@List.{0} (@Bool))) (@Prod.mk.{0, 0} (@Pnp3.Models.Circuit _v4) (@List.{0} (@Bool)) _v6
  _v7))) (@And (@LE.le.{0} (@Nat) (@instLENat) (@Pnp3.Models.Circuit.size _v4 _v6) (@_v0 _v4)) (∀ (_v8 : (@Nat)),
(∀ (_v9 : (@LT.lt.{0} (@Nat) (@instLTNat) _v8 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4))),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead _v1 _v2 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v8)) (@Pnp3.Models.Circuit.eval _v4 _v6 (@Pnp3.Core.vecOfNat _v4
  _v8)))))))))))))))))) := by
  exact @NormalFinalClosure.codec_rows_mirror

-- Complete literal proposition for NormalFinalClosure.codec_rows_mirror; original proof reused.
theorem PartACanonical.Surface.m0306 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Nat))),
(∀ {_v1 : (@Nat)},
(∀ (_v2 : (∀ (_v2 : (@Fin _v1)),
(@Bool))),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (∀ (_v5 : (@Fin (@Pnp4.Frontier.TreeCircuitWitnessCodec.witnessBits _v0
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec _v0) _v4))),
(@Bool))),
(@Iff (@Pnp4.Frontier.TreeCircuitWitnessCodec.verifies _v0 (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  _v0) _v4 (fun (_v6 : (@Fin (@Pnp3.Models.Partial.tableLen _v4))) =>
(@Pnp4.Frontier.ContractExpansion.padRead _v1 _v2 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 (@Fin.val (@Pnp3.Models.Partial.tableLen _v4) _v6)))) _v5) (@Exists.{(0 + 1)} (@Pnp3.Models.Circuit
  _v4) (fun (_v6 : (@Pnp3.Models.Circuit _v4)) =>
(@Exists.{(0 + 1)} (@List.{0} (@Bool)) (fun (_v7 : (@List.{0} (@Bool))) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Pnp3.Models.Circuit _v4) (@List.{0} (@Bool))))
  (@Pnp4.Frontier.ContractExpansion.decodeCircuitFull _v4 (@Pnp4.Frontier.ContractExpansion.bitLength _v4) (@List.ofFn.{0}
  (@Bool) (@Pnp4.Frontier.TreeCircuitWitnessCodec.witnessBits _v0
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec _v0) _v4) _v5)) (@Option.some.{0} (@Prod.{0, 0}
  (@Pnp3.Models.Circuit _v4) (@List.{0} (@Bool))) (@Prod.mk.{0, 0} (@Pnp3.Models.Circuit _v4) (@List.{0} (@Bool)) _v6
  _v7))) (@And (@LE.le.{0} (@Nat) (@instLENat) (@Pnp3.Models.Circuit.size _v4 _v6) (@_v0 _v4)) (∀ (_v8 : (@Nat)),
(∀ (_v9 : (@LT.lt.{0} (@Nat) (@instLTNat) _v8 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4))),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead _v1 _v2 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v8)) (@Pnp3.Models.Circuit.eval _v4 _v6 (@Pnp3.Core.vecOfNat _v4
  _v8)))))))))))))))))) := by
  exact @NormalFinalClosure.codec_rows_mirror

-- Independent literal expected type for NormalFinalClosure.config.
noncomputable def PartACanonical.Types.p0526 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@RawCallerClosure.machine _v0)) _v1 _v2)),
(@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine _v0))
  _v1 _v2))))) := by
  exact @NormalFinalClosure.config

-- Independent literal expected type for NormalFinalClosure.config2.
noncomputable def PartACanonical.Types.p0527 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@RawCallerClosure.machine _v0)) _v1 _v2)),
(@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2
  _v0)) _v1 _v2))))) := by
  exact @NormalFinalClosure.config2

-- Independent literal expected type for NormalFinalClosure.machine.
noncomputable def PartACanonical.Types.p0528 :
(∀ (_v0 : (@Nat)),
(@Pnp3.Complexity.Uniform.V1.UniformTM)) := by
  exact @NormalFinalClosure.machine

-- Independent literal expected type for NormalFinalClosure.machine2.
noncomputable def PartACanonical.Types.p0529 :
(∀ (_v0 : (@Nat)),
(@Pnp3.Complexity.Uniform.V1.UniformTM)) := by
  exact @NormalFinalClosure.machine2

-- Independent literal expected type for NormalFinalClosure.normal_raw.
noncomputable def PartACanonical.Types.p0530 :
(∀ (_v0 : (@Nat)),
(@NormalFinalClosure.Target2.Raw _v0)) := by
  exact @NormalFinalClosure.normal_raw

-- Complete literal proposition for NormalFinalClosure.normal_raw; original proof reused.
theorem PartACanonical.Surface.m0307 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(let _v3 : (@Nat) := (@RawCallerClosure.allocation _v0 _v1);
(let _v4 : (@Pnp3.Complexity.Uniform.V1.UniformTM) := (@RawCallerClosure.machine _v0);
(let _v5 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@NormalFinalClosure.machine2 _v0)) _v1 _v3) := (@Pnp3.Complexity.Uniform.V1.initialConfig (@NormalFinalClosure.machine2
  _v0) _v1 _v3 _v2);
(let _v6 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v4 _v1 _v3 _v2);
(let _v7 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0))) :=
  (@RawCallerClosure.callerState _v0 (@PhysicalCallerClosure.rowsDone _v0));
(let _v8 : (∀ (_v8 : (@Bool)),
(@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0)))) := (fun (_v8 : (@Bool)) =>
(@RawCallerClosure.old _v0 (@CertificateGuardClosure.old _v0 (@TotalIngressClosure.old _v0 (@BodyIngress.old _v0
  (@CarryWindow.embed _v0 (@CanonicalLeaf.result _v0 _v8)))))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v9 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v10 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v9 _v10) (@And (@LE.le.{0} (@Nat) (@instLENat) _v10 (@HMul.hMul.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (17592186044416 : Nat) (@instOfNatNat (17592186044416 : Nat))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat))))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 :
  Nat)))))) (@And (∀ (_v11 : (@Nat)),
(∀ (_v12 : (@LE.le.{0} (@Nat) (@instLENat) _v11 _v9)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@NormalFinalClosure.machine2 _v0)) _v1 _v3) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@NormalFinalClosure.machine2
  _v0) _v1 _v3 _v11 _v5) (@NormalFinalClosure.config2 _v0 _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3
  _v11 _v6))))) (@And (∀ (_v11 : (@Nat)),
(∀ (_v12 : (@LE.le.{0} (@Nat) (@instLENat) _v11 _v9)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3
  _v11 _v6)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v4)))) (@And (∀ (_v11 : (@Nat)),
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) _v11 _v9)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3 _v11 _v6)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v4))
  (@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3 _v11 _v6)) _v7) (∀ (_v13 : (@Bool)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3
  _v11 _v6)) (@_v8 _v13))))))) (@And (∀ (_v11 : (@Nat)),
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) _v11 _v10)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2 _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@NormalFinalClosure.machine2 _v0)) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@NormalFinalClosure.machine2
  _v0) _v1 _v3 _v11 _v5)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@NormalFinalClosure.machine2 _v0))) (@And
  (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2 _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@NormalFinalClosure.machine2 _v0)) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@NormalFinalClosure.machine2
  _v0) _v1 _v3 _v11 _v5)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@NormalFinalClosure.machine2 _v0))) (∀ (_v13 :
  (@Bool)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2 _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@NormalFinalClosure.machine2 _v0)) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@NormalFinalClosure.machine2
  _v0) _v1 _v3 _v11 _v5)) (@NormalFinalClosure.old2 _v0 (@_v8 _v13)))))))) (@Or (@And (@Eq.{(0 + 1)} (@Nat) _v10 _v9)
  (@And (@Exists.{(0 + 1)} (@Bool) (fun (_v11 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3
  _v9 _v6)) (@_v8 _v11)))) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2 _v0)) _v1 _v3)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@NormalFinalClosure.machine2 _v0) _v1 _v3 _v10 _v5)
  (@NormalFinalClosure.config2 _v0 _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3 _v9 _v6))))) (@Or (@And
  (@Eq.{(0 + 1)} (@Nat) _v10 _v9) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3 _v9 _v6)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v4))
  (@And (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.encodedRelationLanguage
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0) _v1 _v2) (@Bool.false)) (@Eq.{(0 +
  1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2
  _v0)) _v1 _v3) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@NormalFinalClosure.machine2 _v0) _v1 _v3 _v10 _v5)
  (@NormalFinalClosure.config2 _v0 _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3 _v9 _v6))))))
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
  _v1 _v15)) (@And (@Eq.{(0 + 1)} (@Nat) _v12 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v11 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Exists.{(0 + 1)} (@Nat) (fun (_v16
  : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v17 : (@Nat)) =>
(@And (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.tagMatches (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 _v12) (@Fin.append.{(0 + 1)} _v11 _v12 (@Bool) _v13 _v14))
  (@Bool.true)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Nat))
  (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros? (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 _v12) (@Fin.append.{(0 + 1)} _v11 _v12 (@Bool) _v13 _v14)) (@Option.some.{0}
  (@Nat) _v17)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Nat) (@Nat)))
  (@Pnp4.Frontier.ContractExpansion.contentHeader? (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v11 _v12) (@Fin.append.{(0 + 1)} _v11 _v12 (@Bool) _v13 _v14)) (@Option.some.{0} (@Prod.{0, 0} (@Nat)
  (@Nat)) (@Prod.mk.{0, 0} (@Nat) (@Nat) _v16 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v17) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))) (let _v18 :
  (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 _v12);
(let _v19 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v1);
(let _v20 : (@Nat) := (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v18 (@Min.min.{0}
  (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v17)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v16)) _v18));
(let _v21 : (@Nat) := (@Cursor.Target.W _v0 _v16);
(@And (@LT.lt.{0} (@Nat) (@instLTNat) (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v17))
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v16)) _v18) _v18) (@And (@LE.le.{0}
  (@Nat) (@instLENat) (@Pnp4.Frontier.ContractExpansion.bitLength _v16) _v20) (@And (@LE.le.{0} (@Nat) (@instLENat) _v21
  _v20) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3 _v9 _v6)) _v7) (@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v18 _v17)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v16) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3)) (fun (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v18 _v17)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v16) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3))) =>
(@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3)) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3
  _v9 _v6)) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v18 _v17) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))
  _v16) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v22)) (@Exists.{(0 + 1)} (@Bool) (fun (_v23 :
  (@Bool)) =>
(@And (@Eq.{(0 + 1)} (@Bool) _v23 (@Pnp3.Complexity.Uniform.V1.encodedRelationLanguage
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0) _v1 _v2)) (@And (@Eq.{(0 + 1)}
  (@Bool) _v23 (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v11 _v12 _v13 _v14))
  (@And (@Iff (@Eq.{(0 + 1)} (@Bool) _v23 (@Bool.true)) (@Exists.{(0 + 1)} (@Nat) (fun (_v24 : (@Nat)) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@Pnp4.Frontier.ContractExpansion.readNatBE (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v17)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v16))
  (@Pnp4.Frontier.ContractExpansion.bitLength _v21)) _v21) (@Pnp4.Frontier.ContractExpansion.padWord (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 _v12) (@Fin.append.{(0 + 1)} _v11 _v12 (@Bool) _v13 _v14)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat)
  (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v17)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v16)) (@Pnp4.Frontier.ContractExpansion.bitLength _v21)) _v21)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v17))
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v16))
  (@Pnp4.Frontier.ContractExpansion.bitLength _v21)) (@Option.some.{0} (@Nat) _v24)) (@And (@LE.le.{0} (@Nat) (@instLENat)
  _v24 _v21) (@And (∀ (_v25 : (@Nat)),
(∀ (_v26 : (@LT.lt.{0} (@Nat) (@instLTNat) _v25 _v24)),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 _v12) (@Fin.append.{(0 + 1)} _v11 _v12 (@Bool) _v13 _v14) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 :
  Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))) _v17)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v16))
  (@Pnp4.Frontier.ContractExpansion.bitLength _v21)) _v25)) (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 _v12) (@Fin.append.{(0 + 1)} _v11 _v12 (@Bool) _v13
  _v14) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v17)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v16))
  (@Pnp4.Frontier.ContractExpansion.bitLength _v21)) _v21) _v25))))) (∀ (_v25 : (@Nat)),
(∀ (_v26 : (@LE.le.{0} (@Nat) (@instLENat) _v24 _v25)),
(∀ (_v27 : (@LT.lt.{0} (@Nat) (@instLTNat) _v25 _v21)),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 _v12) (@Fin.append.{(0 + 1)} _v11 _v12 (@Bool) _v13 _v14) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 :
  Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))) _v17)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v16))
  (@Pnp4.Frontier.ContractExpansion.bitLength _v21)) _v25)) (@Bool.false))))))))))) (@Eq.{(0 + 1)}
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2
  _v0)) _v1 _v3) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@NormalFinalClosure.machine2 _v0) _v1 _v3 _v10 _v5)
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2
  _v0)) _v1 _v3 (@ite.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2
  _v0))) (@Eq.{(0 + 1)} (@Bool) _v23 (@Bool.true)) (@instDecidableEqBool _v23 (@Bool.true))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@NormalFinalClosure.machine2 _v0))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@NormalFinalClosure.machine2 _v0))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v18 _v17) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v16) (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v22) (@NormalFinalClosure.Target.cleared _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3 _v9 _v6)) _v19 _v20
  _v16)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @NormalFinalClosure.normal_raw

-- Independent literal expected type for NormalFinalClosure.normal_raw_full.
noncomputable def PartACanonical.Types.p0531 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (∀ (_v2 : (@Fin _v1)),
(@Bool))),
(let _v3 : (@Nat) := (@RawCallerClosure.allocation _v0 _v1);
(let _v4 : (@Pnp3.Complexity.Uniform.V1.UniformTM) := (@RawCallerClosure.machine _v0);
(let _v5 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@NormalFinalClosure.machine2 _v0)) _v1 _v3) := (@Pnp3.Complexity.Uniform.V1.initialConfig (@NormalFinalClosure.machine2
  _v0) _v1 _v3 _v2);
(let _v6 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v4 _v1 _v3 _v2);
(let _v7 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0))) :=
  (@RawCallerClosure.callerState _v0 (@PhysicalCallerClosure.rowsDone _v0));
(let _v8 : (∀ (_v8 : (@Bool)),
(@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0)))) := (fun (_v8 : (@Bool)) =>
(@RawCallerClosure.old _v0 (@CertificateGuardClosure.old _v0 (@TotalIngressClosure.old _v0 (@BodyIngress.old _v0
  (@CarryWindow.embed _v0 (@CanonicalLeaf.result _v0 _v8)))))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v9 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v10 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v9 _v10) (@And (@LE.le.{0} (@Nat) (@instLENat) _v10 (@HMul.hMul.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (17592186044416 : Nat) (@instOfNatNat (17592186044416 : Nat))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat))))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 :
  Nat)))))) (@And (∀ (_v11 : (@Nat)),
(∀ (_v12 : (@LE.le.{0} (@Nat) (@instLENat) _v11 _v9)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@NormalFinalClosure.machine2 _v0)) _v1 _v3) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@NormalFinalClosure.machine2
  _v0) _v1 _v3 _v11 _v5) (@NormalFinalClosure.config2 _v0 _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3
  _v11 _v6))))) (@And (∀ (_v11 : (@Nat)),
(∀ (_v12 : (@LE.le.{0} (@Nat) (@instLENat) _v11 _v9)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3
  _v11 _v6)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v4)))) (@And (∀ (_v11 : (@Nat)),
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) _v11 _v9)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3 _v11 _v6)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v4))
  (@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3 _v11 _v6)) _v7) (∀ (_v13 : (@Bool)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3
  _v11 _v6)) (@_v8 _v13))))))) (@And (∀ (_v11 : (@Nat)),
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) _v11 _v10)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2 _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@NormalFinalClosure.machine2 _v0)) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@NormalFinalClosure.machine2
  _v0) _v1 _v3 _v11 _v5)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@NormalFinalClosure.machine2 _v0))) (@And
  (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2 _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@NormalFinalClosure.machine2 _v0)) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@NormalFinalClosure.machine2
  _v0) _v1 _v3 _v11 _v5)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@NormalFinalClosure.machine2 _v0))) (∀ (_v13 :
  (@Bool)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2 _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@NormalFinalClosure.machine2 _v0)) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@NormalFinalClosure.machine2
  _v0) _v1 _v3 _v11 _v5)) (@NormalFinalClosure.old2 _v0 (@_v8 _v13)))))))) (@Or (@And (@Eq.{(0 + 1)} (@Nat) _v10 _v9)
  (@And (@Exists.{(0 + 1)} (@Bool) (fun (_v11 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3
  _v9 _v6)) (@_v8 _v11)))) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2 _v0)) _v1 _v3)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@NormalFinalClosure.machine2 _v0) _v1 _v3 _v10 _v5)
  (@NormalFinalClosure.config2 _v0 _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3 _v9 _v6))))) (@Or (@And
  (@Eq.{(0 + 1)} (@Nat) _v10 _v9) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3 _v9 _v6)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v4))
  (@And (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.encodedRelationLanguage
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0) _v1 _v2) (@Bool.false)) (@Eq.{(0 +
  1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2
  _v0)) _v1 _v3) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@NormalFinalClosure.machine2 _v0) _v1 _v3 _v10 _v5)
  (@NormalFinalClosure.config2 _v0 _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3 _v9 _v6))))))
  (@Exists.{(0 + 1)} (@Nat) (fun (_v11 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v12 : (@Nat)) =>
(@Exists.{(0 + 1)} (∀ (_v13 : (@Fin _v11)),
(@Bool)) (fun (_v13 : (∀ (_v13 : (@Fin _v11)),
(@Bool))) =>
(@Exists.{(0 + 1)} (∀ (_v14 : (@Fin _v12)),
(@Bool)) (fun (_v14 : (∀ (_v14 : (@Fin _v12)),
(@Bool))) =>
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
(@Pnp3.Complexity.Uniform.V1.Bitstring _v16)) _v12 _v14)))) (@And (@Eq.{(0 + 1)} (∀ (_v16 : (@Fin _v1)),
(@Bool)) _v2 (@Eq.rec.{(0 + 1), (0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v11 _v12) (fun
  (_v16 : (@Nat)) =>
(fun (_v17 : (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v11 _v12) _v16)) =>
(∀ (_v18 : (@Fin _v16)),
(@Bool)))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v11 _v12 _v13 _v14) _v1 _v15)) (@And (@Eq.{(0 + 1)}
  (@Nat) _v12 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Exists.{(0 + 1)} (@Nat) (fun (_v16 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v17 : (@Nat)) =>
(@And (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.tagMatches (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 _v12) (@Fin.append.{(0 + 1)} _v11 _v12 (@Bool) _v13 _v14))
  (@Bool.true)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Nat))
  (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros? (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 _v12) (@Fin.append.{(0 + 1)} _v11 _v12 (@Bool) _v13 _v14)) (@Option.some.{0}
  (@Nat) _v17)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Nat) (@Nat)))
  (@Pnp4.Frontier.ContractExpansion.contentHeader? (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v11 _v12) (@Fin.append.{(0 + 1)} _v11 _v12 (@Bool) _v13 _v14)) (@Option.some.{0} (@Prod.{0, 0} (@Nat)
  (@Nat)) (@Prod.mk.{0, 0} (@Nat) (@Nat) _v16 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v17) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))) (let _v18 :
  (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 _v12);
(let _v19 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v1);
(let _v20 : (@Nat) := (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v18 (@Min.min.{0}
  (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v17)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v16)) _v18));
(let _v21 : (@Nat) := (@Cursor.Target.W _v0 _v16);
(@And (@LT.lt.{0} (@Nat) (@instLTNat) (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v17))
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v16)) _v18) _v18) (@And (@LE.le.{0}
  (@Nat) (@instLENat) (@Pnp4.Frontier.ContractExpansion.bitLength _v16) _v20) (@And (@LE.le.{0} (@Nat) (@instLENat) _v21
  _v20) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3 _v9 _v6)) _v7) (@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v18 _v17)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v16) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3)) (fun (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v18 _v17)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v16) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3))) =>
(@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3)) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3
  _v9 _v6)) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v18 _v17) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))
  _v16) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v22)) (@Exists.{(0 + 1)} (@Bool) (fun (_v23 :
  (@Bool)) =>
(@And (@Eq.{(0 + 1)} (@Bool) _v23 (@Pnp3.Complexity.Uniform.V1.encodedRelationLanguage
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0) _v1 _v2)) (@And (@Eq.{(0 + 1)}
  (@Bool) _v23 (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v11 _v12 _v13 _v14))
  (@And (@Iff (@Eq.{(0 + 1)} (@Bool) _v23 (@Bool.true)) (@Exists.{(0 + 1)} (@Nat) (fun (_v24 : (@Nat)) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@Pnp4.Frontier.ContractExpansion.readNatBE (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v17)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v16))
  (@Pnp4.Frontier.ContractExpansion.bitLength _v21)) _v21) (@Pnp4.Frontier.ContractExpansion.padWord (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 _v12) (@Fin.append.{(0 + 1)} _v11 _v12 (@Bool) _v13 _v14)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat)
  (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v17)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v16)) (@Pnp4.Frontier.ContractExpansion.bitLength _v21)) _v21)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v17))
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v16))
  (@Pnp4.Frontier.ContractExpansion.bitLength _v21)) (@Option.some.{0} (@Nat) _v24)) (@And (@LE.le.{0} (@Nat) (@instLENat)
  _v24 _v21) (@And (∀ (_v25 : (@Nat)),
(∀ (_v26 : (@LT.lt.{0} (@Nat) (@instLTNat) _v25 _v24)),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 _v12) (@Fin.append.{(0 + 1)} _v11 _v12 (@Bool) _v13 _v14) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 :
  Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))) _v17)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v16))
  (@Pnp4.Frontier.ContractExpansion.bitLength _v21)) _v25)) (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 _v12) (@Fin.append.{(0 + 1)} _v11 _v12 (@Bool) _v13
  _v14) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v17)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v16))
  (@Pnp4.Frontier.ContractExpansion.bitLength _v21)) _v21) _v25))))) (∀ (_v25 : (@Nat)),
(∀ (_v26 : (@LE.le.{0} (@Nat) (@instLENat) _v24 _v25)),
(∀ (_v27 : (@LT.lt.{0} (@Nat) (@instLTNat) _v25 _v21)),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 _v12) (@Fin.append.{(0 + 1)} _v11 _v12 (@Bool) _v13 _v14) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 :
  Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))) _v17)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v16))
  (@Pnp4.Frontier.ContractExpansion.bitLength _v21)) _v25)) (@Bool.false))))))))))) (@Eq.{(0 + 1)}
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2
  _v0)) _v1 _v3) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@NormalFinalClosure.machine2 _v0) _v1 _v3 _v10 _v5)
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2
  _v0)) _v1 _v3 (@ite.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2
  _v0))) (@Eq.{(0 + 1)} (@Bool) _v23 (@Bool.true)) (@instDecidableEqBool _v23 (@Bool.true))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@NormalFinalClosure.machine2 _v0))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@NormalFinalClosure.machine2 _v0))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v18 _v17) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v16) (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v22) (@NormalFinalClosure.Target.cleared _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3 _v9 _v6)) _v19 _v20
  _v16)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @NormalFinalClosure.normal_raw_full

-- Complete literal proposition for NormalFinalClosure.normal_raw_full; original proof reused.
theorem PartACanonical.Surface.m0308 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (∀ (_v2 : (@Fin _v1)),
(@Bool))),
(let _v3 : (@Nat) := (@RawCallerClosure.allocation _v0 _v1);
(let _v4 : (@Pnp3.Complexity.Uniform.V1.UniformTM) := (@RawCallerClosure.machine _v0);
(let _v5 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@NormalFinalClosure.machine2 _v0)) _v1 _v3) := (@Pnp3.Complexity.Uniform.V1.initialConfig (@NormalFinalClosure.machine2
  _v0) _v1 _v3 _v2);
(let _v6 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v4 _v1 _v3 _v2);
(let _v7 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0))) :=
  (@RawCallerClosure.callerState _v0 (@PhysicalCallerClosure.rowsDone _v0));
(let _v8 : (∀ (_v8 : (@Bool)),
(@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0)))) := (fun (_v8 : (@Bool)) =>
(@RawCallerClosure.old _v0 (@CertificateGuardClosure.old _v0 (@TotalIngressClosure.old _v0 (@BodyIngress.old _v0
  (@CarryWindow.embed _v0 (@CanonicalLeaf.result _v0 _v8)))))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v9 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v10 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v9 _v10) (@And (@LE.le.{0} (@Nat) (@instLENat) _v10 (@HMul.hMul.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (17592186044416 : Nat) (@instOfNatNat (17592186044416 : Nat))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat))))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 :
  Nat)))))) (@And (∀ (_v11 : (@Nat)),
(∀ (_v12 : (@LE.le.{0} (@Nat) (@instLENat) _v11 _v9)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@NormalFinalClosure.machine2 _v0)) _v1 _v3) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@NormalFinalClosure.machine2
  _v0) _v1 _v3 _v11 _v5) (@NormalFinalClosure.config2 _v0 _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3
  _v11 _v6))))) (@And (∀ (_v11 : (@Nat)),
(∀ (_v12 : (@LE.le.{0} (@Nat) (@instLENat) _v11 _v9)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3
  _v11 _v6)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v4)))) (@And (∀ (_v11 : (@Nat)),
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) _v11 _v9)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3 _v11 _v6)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v4))
  (@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3 _v11 _v6)) _v7) (∀ (_v13 : (@Bool)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3
  _v11 _v6)) (@_v8 _v13))))))) (@And (∀ (_v11 : (@Nat)),
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) _v11 _v10)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2 _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@NormalFinalClosure.machine2 _v0)) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@NormalFinalClosure.machine2
  _v0) _v1 _v3 _v11 _v5)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@NormalFinalClosure.machine2 _v0))) (@And
  (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2 _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@NormalFinalClosure.machine2 _v0)) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@NormalFinalClosure.machine2
  _v0) _v1 _v3 _v11 _v5)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@NormalFinalClosure.machine2 _v0))) (∀ (_v13 :
  (@Bool)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2 _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@NormalFinalClosure.machine2 _v0)) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@NormalFinalClosure.machine2
  _v0) _v1 _v3 _v11 _v5)) (@NormalFinalClosure.old2 _v0 (@_v8 _v13)))))))) (@Or (@And (@Eq.{(0 + 1)} (@Nat) _v10 _v9)
  (@And (@Exists.{(0 + 1)} (@Bool) (fun (_v11 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3
  _v9 _v6)) (@_v8 _v11)))) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2 _v0)) _v1 _v3)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@NormalFinalClosure.machine2 _v0) _v1 _v3 _v10 _v5)
  (@NormalFinalClosure.config2 _v0 _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3 _v9 _v6))))) (@Or (@And
  (@Eq.{(0 + 1)} (@Nat) _v10 _v9) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3 _v9 _v6)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v4))
  (@And (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.encodedRelationLanguage
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0) _v1 _v2) (@Bool.false)) (@Eq.{(0 +
  1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2
  _v0)) _v1 _v3) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@NormalFinalClosure.machine2 _v0) _v1 _v3 _v10 _v5)
  (@NormalFinalClosure.config2 _v0 _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3 _v9 _v6))))))
  (@Exists.{(0 + 1)} (@Nat) (fun (_v11 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v12 : (@Nat)) =>
(@Exists.{(0 + 1)} (∀ (_v13 : (@Fin _v11)),
(@Bool)) (fun (_v13 : (∀ (_v13 : (@Fin _v11)),
(@Bool))) =>
(@Exists.{(0 + 1)} (∀ (_v14 : (@Fin _v12)),
(@Bool)) (fun (_v14 : (∀ (_v14 : (@Fin _v12)),
(@Bool))) =>
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
(@Pnp3.Complexity.Uniform.V1.Bitstring _v16)) _v12 _v14)))) (@And (@Eq.{(0 + 1)} (∀ (_v16 : (@Fin _v1)),
(@Bool)) _v2 (@Eq.rec.{(0 + 1), (0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v11 _v12) (fun
  (_v16 : (@Nat)) =>
(fun (_v17 : (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v11 _v12) _v16)) =>
(∀ (_v18 : (@Fin _v16)),
(@Bool)))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v11 _v12 _v13 _v14) _v1 _v15)) (@And (@Eq.{(0 + 1)}
  (@Nat) _v12 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Exists.{(0 + 1)} (@Nat) (fun (_v16 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v17 : (@Nat)) =>
(@And (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.tagMatches (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 _v12) (@Fin.append.{(0 + 1)} _v11 _v12 (@Bool) _v13 _v14))
  (@Bool.true)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Nat))
  (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros? (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 _v12) (@Fin.append.{(0 + 1)} _v11 _v12 (@Bool) _v13 _v14)) (@Option.some.{0}
  (@Nat) _v17)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Nat) (@Nat)))
  (@Pnp4.Frontier.ContractExpansion.contentHeader? (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v11 _v12) (@Fin.append.{(0 + 1)} _v11 _v12 (@Bool) _v13 _v14)) (@Option.some.{0} (@Prod.{0, 0} (@Nat)
  (@Nat)) (@Prod.mk.{0, 0} (@Nat) (@Nat) _v16 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v17) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))) (let _v18 :
  (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 _v12);
(let _v19 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v1);
(let _v20 : (@Nat) := (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v18 (@Min.min.{0}
  (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v17)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v16)) _v18));
(let _v21 : (@Nat) := (@Cursor.Target.W _v0 _v16);
(@And (@LT.lt.{0} (@Nat) (@instLTNat) (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v17))
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v16)) _v18) _v18) (@And (@LE.le.{0}
  (@Nat) (@instLENat) (@Pnp4.Frontier.ContractExpansion.bitLength _v16) _v20) (@And (@LE.le.{0} (@Nat) (@instLENat) _v21
  _v20) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3 _v9 _v6)) _v7) (@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v18 _v17)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v16) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3)) (fun (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v18 _v17)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v16) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3))) =>
(@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3)) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3
  _v9 _v6)) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v18 _v17) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))
  _v16) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v22)) (@Exists.{(0 + 1)} (@Bool) (fun (_v23 :
  (@Bool)) =>
(@And (@Eq.{(0 + 1)} (@Bool) _v23 (@Pnp3.Complexity.Uniform.V1.encodedRelationLanguage
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0) _v1 _v2)) (@And (@Eq.{(0 + 1)}
  (@Bool) _v23 (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v11 _v12 _v13 _v14))
  (@And (@Iff (@Eq.{(0 + 1)} (@Bool) _v23 (@Bool.true)) (@Exists.{(0 + 1)} (@Nat) (fun (_v24 : (@Nat)) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@Pnp4.Frontier.ContractExpansion.readNatBE (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v17)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v16))
  (@Pnp4.Frontier.ContractExpansion.bitLength _v21)) _v21) (@Pnp4.Frontier.ContractExpansion.padWord (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 _v12) (@Fin.append.{(0 + 1)} _v11 _v12 (@Bool) _v13 _v14)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat)
  (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v17)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v16)) (@Pnp4.Frontier.ContractExpansion.bitLength _v21)) _v21)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v17))
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v16))
  (@Pnp4.Frontier.ContractExpansion.bitLength _v21)) (@Option.some.{0} (@Nat) _v24)) (@And (@LE.le.{0} (@Nat) (@instLENat)
  _v24 _v21) (@And (∀ (_v25 : (@Nat)),
(∀ (_v26 : (@LT.lt.{0} (@Nat) (@instLTNat) _v25 _v24)),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 _v12) (@Fin.append.{(0 + 1)} _v11 _v12 (@Bool) _v13 _v14) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 :
  Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))) _v17)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v16))
  (@Pnp4.Frontier.ContractExpansion.bitLength _v21)) _v25)) (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 _v12) (@Fin.append.{(0 + 1)} _v11 _v12 (@Bool) _v13
  _v14) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v17)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v16))
  (@Pnp4.Frontier.ContractExpansion.bitLength _v21)) _v21) _v25))))) (∀ (_v25 : (@Nat)),
(∀ (_v26 : (@LE.le.{0} (@Nat) (@instLENat) _v24 _v25)),
(∀ (_v27 : (@LT.lt.{0} (@Nat) (@instLTNat) _v25 _v21)),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 _v12) (@Fin.append.{(0 + 1)} _v11 _v12 (@Bool) _v13 _v14) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 :
  Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))) _v17)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v16))
  (@Pnp4.Frontier.ContractExpansion.bitLength _v21)) _v25)) (@Bool.false))))))))))) (@Eq.{(0 + 1)}
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2
  _v0)) _v1 _v3) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@NormalFinalClosure.machine2 _v0) _v1 _v3 _v10 _v5)
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2
  _v0)) _v1 _v3 (@ite.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2
  _v0))) (@Eq.{(0 + 1)} (@Bool) _v23 (@Bool.true)) (@instDecidableEqBool _v23 (@Bool.true))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@NormalFinalClosure.machine2 _v0))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@NormalFinalClosure.machine2 _v0))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v18 _v17) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v16) (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v22) (@NormalFinalClosure.Target.cleared _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3 _v9 _v6)) _v19 _v20
  _v16)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @NormalFinalClosure.normal_raw_full

-- Independent literal expected type for NormalFinalClosure.old.
noncomputable def PartACanonical.Types.p0532 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0)))),
(@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine _v0))))) := by
  exact @NormalFinalClosure.old

-- Independent literal expected type for NormalFinalClosure.old2.
noncomputable def PartACanonical.Types.p0533 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0)))),
(@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2 _v0))))) := by
  exact @NormalFinalClosure.old2

-- Independent literal expected type for NormalFinalClosure.raw_prefix.
noncomputable def PartACanonical.Types.p0534 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v5 : (∀ (_v5 : (@Nat)),
(∀ (_v6 : (@LT.lt.{0} (@Nat) (@instLTNat) _v5 _v3)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine
  _v0)) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1 _v2 _v5
  (@Pnp3.Complexity.Uniform.V1.initialConfig (@RawCallerClosure.machine _v0) _v1 _v2 _v4))) (@RawCallerClosure.callerState
  _v0 (@PhysicalCallerClosure.rowsDone _v0)))))),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@LE.le.{0} (@Nat) (@instLENat) _v6 _v3)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@NormalFinalClosure.machine _v0)) _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@NormalFinalClosure.machine _v0)
  _v1 _v2 _v6 (@Pnp3.Complexity.Uniform.V1.initialConfig (@NormalFinalClosure.machine _v0) _v1 _v2 _v4))
  (@NormalFinalClosure.config _v0 _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1
  _v2 _v6 (@Pnp3.Complexity.Uniform.V1.initialConfig (@RawCallerClosure.machine _v0) _v1 _v2 _v4)))))))))))) := by
  exact @NormalFinalClosure.raw_prefix

-- Complete literal proposition for NormalFinalClosure.raw_prefix; original proof reused.
theorem PartACanonical.Surface.m0309 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v5 : (∀ (_v5 : (@Nat)),
(∀ (_v6 : (@LT.lt.{0} (@Nat) (@instLTNat) _v5 _v3)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine
  _v0)) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1 _v2 _v5
  (@Pnp3.Complexity.Uniform.V1.initialConfig (@RawCallerClosure.machine _v0) _v1 _v2 _v4))) (@RawCallerClosure.callerState
  _v0 (@PhysicalCallerClosure.rowsDone _v0)))))),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@LE.le.{0} (@Nat) (@instLENat) _v6 _v3)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@NormalFinalClosure.machine _v0)) _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@NormalFinalClosure.machine _v0)
  _v1 _v2 _v6 (@Pnp3.Complexity.Uniform.V1.initialConfig (@NormalFinalClosure.machine _v0) _v1 _v2 _v4))
  (@NormalFinalClosure.config _v0 _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1
  _v2 _v6 (@Pnp3.Complexity.Uniform.V1.initialConfig (@RawCallerClosure.machine _v0) _v1 _v2 _v4)))))))))))) := by
  exact @NormalFinalClosure.raw_prefix

-- Independent literal expected type for NormalFinalClosure.raw_prefix2.
noncomputable def PartACanonical.Types.p0535 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v5 : (∀ (_v5 : (@Nat)),
(∀ (_v6 : (@LT.lt.{0} (@Nat) (@instLTNat) _v5 _v3)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine
  _v0)) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1 _v2 _v5
  (@Pnp3.Complexity.Uniform.V1.initialConfig (@RawCallerClosure.machine _v0) _v1 _v2 _v4))) (@RawCallerClosure.callerState
  _v0 (@PhysicalCallerClosure.rowsDone _v0)))))),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@LE.le.{0} (@Nat) (@instLENat) _v6 _v3)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@NormalFinalClosure.machine2 _v0)) _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@NormalFinalClosure.machine2
  _v0) _v1 _v2 _v6 (@Pnp3.Complexity.Uniform.V1.initialConfig (@NormalFinalClosure.machine2 _v0) _v1 _v2 _v4))
  (@NormalFinalClosure.config2 _v0 _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1
  _v2 _v6 (@Pnp3.Complexity.Uniform.V1.initialConfig (@RawCallerClosure.machine _v0) _v1 _v2 _v4)))))))))))) := by
  exact @NormalFinalClosure.raw_prefix2

-- Complete literal proposition for NormalFinalClosure.raw_prefix2; original proof reused.
theorem PartACanonical.Surface.m0310 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v5 : (∀ (_v5 : (@Nat)),
(∀ (_v6 : (@LT.lt.{0} (@Nat) (@instLTNat) _v5 _v3)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine
  _v0)) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1 _v2 _v5
  (@Pnp3.Complexity.Uniform.V1.initialConfig (@RawCallerClosure.machine _v0) _v1 _v2 _v4))) (@RawCallerClosure.callerState
  _v0 (@PhysicalCallerClosure.rowsDone _v0)))))),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@LE.le.{0} (@Nat) (@instLENat) _v6 _v3)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@NormalFinalClosure.machine2 _v0)) _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@NormalFinalClosure.machine2
  _v0) _v1 _v2 _v6 (@Pnp3.Complexity.Uniform.V1.initialConfig (@NormalFinalClosure.machine2 _v0) _v1 _v2 _v4))
  (@NormalFinalClosure.config2 _v0 _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1
  _v2 _v6 (@Pnp3.Complexity.Uniform.V1.initialConfig (@RawCallerClosure.machine _v0) _v1 _v2 _v4)))))))))))) := by
  exact @NormalFinalClosure.raw_prefix2

-- Independent literal expected type for NormalFinalClosure.raw_prefix2_mirror.
noncomputable def PartACanonical.Types.p0536 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v5 : (∀ (_v5 : (@Nat)),
(∀ (_v6 : (@LT.lt.{0} (@Nat) (@instLTNat) _v5 _v3)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine
  _v0)) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1 _v2 _v5
  (@Pnp3.Complexity.Uniform.V1.initialConfig (@RawCallerClosure.machine _v0) _v1 _v2 _v4))) (@RawCallerClosure.callerState
  _v0 (@PhysicalCallerClosure.rowsDone _v0)))))),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@LE.le.{0} (@Nat) (@instLENat) _v6 _v3)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@NormalFinalClosure.machine2 _v0)) _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@NormalFinalClosure.machine2
  _v0) _v1 _v2 _v6 (@Pnp3.Complexity.Uniform.V1.initialConfig (@NormalFinalClosure.machine2 _v0) _v1 _v2 _v4))
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2
  _v0)) _v1 _v2 (@NormalFinalClosure.old2 _v0 (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0)) _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1 _v2 _v6
  (@Pnp3.Complexity.Uniform.V1.initialConfig (@RawCallerClosure.machine _v0) _v1 _v2 _v4))))
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine
  _v0)) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1 _v2 _v6
  (@Pnp3.Complexity.Uniform.V1.initialConfig (@RawCallerClosure.machine _v0) _v1 _v2 _v4)))
  (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine
  _v0)) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1 _v2 _v6
  (@Pnp3.Complexity.Uniform.V1.initialConfig (@RawCallerClosure.machine _v0) _v1 _v2 _v4))))))))))))) := by
  exact @NormalFinalClosure.raw_prefix2_mirror

-- Complete literal proposition for NormalFinalClosure.raw_prefix2_mirror; original proof reused.
theorem PartACanonical.Surface.m0311 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v5 : (∀ (_v5 : (@Nat)),
(∀ (_v6 : (@LT.lt.{0} (@Nat) (@instLTNat) _v5 _v3)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine
  _v0)) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1 _v2 _v5
  (@Pnp3.Complexity.Uniform.V1.initialConfig (@RawCallerClosure.machine _v0) _v1 _v2 _v4))) (@RawCallerClosure.callerState
  _v0 (@PhysicalCallerClosure.rowsDone _v0)))))),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@LE.le.{0} (@Nat) (@instLENat) _v6 _v3)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@NormalFinalClosure.machine2 _v0)) _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@NormalFinalClosure.machine2
  _v0) _v1 _v2 _v6 (@Pnp3.Complexity.Uniform.V1.initialConfig (@NormalFinalClosure.machine2 _v0) _v1 _v2 _v4))
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2
  _v0)) _v1 _v2 (@NormalFinalClosure.old2 _v0 (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0)) _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1 _v2 _v6
  (@Pnp3.Complexity.Uniform.V1.initialConfig (@RawCallerClosure.machine _v0) _v1 _v2 _v4))))
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine
  _v0)) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1 _v2 _v6
  (@Pnp3.Complexity.Uniform.V1.initialConfig (@RawCallerClosure.machine _v0) _v1 _v2 _v4)))
  (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine
  _v0)) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1 _v2 _v6
  (@Pnp3.Complexity.Uniform.V1.initialConfig (@RawCallerClosure.machine _v0) _v1 _v2 _v4))))))))))))) := by
  exact @NormalFinalClosure.raw_prefix2_mirror

-- Independent literal expected type for NormalFinalClosure.raw_prefix_mirror.
noncomputable def PartACanonical.Types.p0537 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v5 : (∀ (_v5 : (@Nat)),
(∀ (_v6 : (@LT.lt.{0} (@Nat) (@instLTNat) _v5 _v3)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine
  _v0)) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1 _v2 _v5
  (@Pnp3.Complexity.Uniform.V1.initialConfig (@RawCallerClosure.machine _v0) _v1 _v2 _v4))) (@RawCallerClosure.callerState
  _v0 (@PhysicalCallerClosure.rowsDone _v0)))))),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@LE.le.{0} (@Nat) (@instLENat) _v6 _v3)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@NormalFinalClosure.machine _v0)) _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@NormalFinalClosure.machine _v0)
  _v1 _v2 _v6 (@Pnp3.Complexity.Uniform.V1.initialConfig (@NormalFinalClosure.machine _v0) _v1 _v2 _v4))
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine
  _v0)) _v1 _v2 (@NormalFinalClosure.old _v0 (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0)) _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1 _v2 _v6
  (@Pnp3.Complexity.Uniform.V1.initialConfig (@RawCallerClosure.machine _v0) _v1 _v2 _v4))))
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine
  _v0)) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1 _v2 _v6
  (@Pnp3.Complexity.Uniform.V1.initialConfig (@RawCallerClosure.machine _v0) _v1 _v2 _v4)))
  (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine
  _v0)) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1 _v2 _v6
  (@Pnp3.Complexity.Uniform.V1.initialConfig (@RawCallerClosure.machine _v0) _v1 _v2 _v4))))))))))))) := by
  exact @NormalFinalClosure.raw_prefix_mirror

-- Complete literal proposition for NormalFinalClosure.raw_prefix_mirror; original proof reused.
theorem PartACanonical.Surface.m0312 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v5 : (∀ (_v5 : (@Nat)),
(∀ (_v6 : (@LT.lt.{0} (@Nat) (@instLTNat) _v5 _v3)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine
  _v0)) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1 _v2 _v5
  (@Pnp3.Complexity.Uniform.V1.initialConfig (@RawCallerClosure.machine _v0) _v1 _v2 _v4))) (@RawCallerClosure.callerState
  _v0 (@PhysicalCallerClosure.rowsDone _v0)))))),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@LE.le.{0} (@Nat) (@instLENat) _v6 _v3)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@NormalFinalClosure.machine _v0)) _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@NormalFinalClosure.machine _v0)
  _v1 _v2 _v6 (@Pnp3.Complexity.Uniform.V1.initialConfig (@NormalFinalClosure.machine _v0) _v1 _v2 _v4))
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine
  _v0)) _v1 _v2 (@NormalFinalClosure.old _v0 (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0)) _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1 _v2 _v6
  (@Pnp3.Complexity.Uniform.V1.initialConfig (@RawCallerClosure.machine _v0) _v1 _v2 _v4))))
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine
  _v0)) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1 _v2 _v6
  (@Pnp3.Complexity.Uniform.V1.initialConfig (@RawCallerClosure.machine _v0) _v1 _v2 _v4)))
  (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine
  _v0)) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@RawCallerClosure.machine _v0) _v1 _v2 _v6
  (@Pnp3.Complexity.Uniform.V1.initialConfig (@RawCallerClosure.machine _v0) _v1 _v2 _v4))))))))))))) := by
  exact @NormalFinalClosure.raw_prefix_mirror

-- Independent literal expected type for NormalFinalClosure.rho_append.
noncomputable def PartACanonical.Types.p0538 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v2)),
(∀ (_v5 : (@Eq.{(0 + 1)} (@Nat) _v2 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v1 _v2 _v3
  _v4) (@Pnp4.Frontier.ContractExpansion.contentSemanticAccepts (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2
  (@Bool) _v3 _v4))))))))) := by
  exact @NormalFinalClosure.rho_append

-- Complete literal proposition for NormalFinalClosure.rho_append; original proof reused.
theorem PartACanonical.Surface.m0313 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v2)),
(∀ (_v5 : (@Eq.{(0 + 1)} (@Nat) _v2 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v1 _v2 _v3
  _v4) (@Pnp4.Frontier.ContractExpansion.contentSemanticAccepts (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2
  (@Bool) _v3 _v4))))))))) := by
  exact @NormalFinalClosure.rho_append

-- Independent literal expected type for NormalFinalClosure.rho_append_mirror.
noncomputable def PartACanonical.Types.p0539 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v2)),
(∀ (_v5 : (@Eq.{(0 + 1)} (@Nat) _v2 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v1 _v2 _v3
  _v4) (@Pnp4.Frontier.ContractExpansion.contentSemanticAccepts (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2
  (@Bool) _v3 _v4))))))))) := by
  exact @NormalFinalClosure.rho_append_mirror

-- Complete literal proposition for NormalFinalClosure.rho_append_mirror; original proof reused.
theorem PartACanonical.Surface.m0314 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v2)),
(∀ (_v5 : (@Eq.{(0 + 1)} (@Nat) _v2 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v1 _v2 _v3
  _v4) (@Pnp4.Frontier.ContractExpansion.contentSemanticAccepts (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2
  (@Bool) _v3 _v4))))))))) := by
  exact @NormalFinalClosure.rho_append_mirror

-- Independent literal expected type for NormalFinalClosure.rows_prefix_rho.
noncomputable def PartACanonical.Types.p0540 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v6 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v2)),
(∀ (_v7 : (@Eq.{(0 + 1)} (@Nat) _v2 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v8 : (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Nat) (@Nat))) (@Pnp4.Frontier.ContractExpansion.contentHeader?
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2
  (@Bool) _v5 _v6)) (@Option.some.{0} (@Prod.{0, 0} (@Nat) (@Nat)) (@Prod.mk.{0, 0} (@Nat) (@Nat) _v3 (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4) (@OfNat.ofNat.{0} (@Nat) (1 :
  Nat) (@instOfNatNat (1 : Nat)))))))),
(∀ (_v9 : (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.tagMatches (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v5 _v6))
  (@Bool.true))),
(∀ (_v10 : (@Pnp3.Models.Circuit _v3)),
(∀ (_v11 : (@List.{0} (@Bool))),
(∀ (_v12 : (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Pnp3.Models.Circuit _v3) (@List.{0} (@Bool))))
  (@Pnp4.Frontier.ContractExpansion.decodeCircuitFull _v3 (@Pnp4.Frontier.ContractExpansion.bitLength _v3)
  (@SerializedBody.window (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)
  (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v5 _v6) (@Cursor.Target.M _v0 _v3 _v4) (@Cursor.Target.W _v0 _v3)))
  (@Option.some.{0} (@Prod.{0, 0} (@Pnp3.Models.Circuit _v3) (@List.{0} (@Bool))) (@Prod.mk.{0, 0} (@Pnp3.Models.Circuit
  _v3) (@List.{0} (@Bool)) _v10 _v11)))),
(∀ (_v13 : (@LE.le.{0} (@Nat) (@instLENat) (@Pnp3.Models.Circuit.size _v3 _v10) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v3 _v0) _v0))),
(∀ (_v14 : (∀ (_v14 : (@Nat)),
(∀ (_v15 : (@LT.lt.{0} (@Nat) (@instLTNat) _v14 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat)
  (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v3))),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v5 _v6) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)) _v14))
  (@Pnp3.Models.Circuit.eval _v3 _v10 (@Pnp3.Core.vecOfNat _v3 _v14)))))),
(@Iff (@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v1 _v2
  _v5 _v6) (@Bool.true)) (@NormalFinalClosure.Target.PrefixOK (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v5 _v6) _v3 _v4 (@Cursor.Target.W _v0
  _v3)))))))))))))))))) := by
  exact @NormalFinalClosure.rows_prefix_rho

-- Complete literal proposition for NormalFinalClosure.rows_prefix_rho; original proof reused.
theorem PartACanonical.Surface.m0315 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v6 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v2)),
(∀ (_v7 : (@Eq.{(0 + 1)} (@Nat) _v2 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v8 : (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Nat) (@Nat))) (@Pnp4.Frontier.ContractExpansion.contentHeader?
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2
  (@Bool) _v5 _v6)) (@Option.some.{0} (@Prod.{0, 0} (@Nat) (@Nat)) (@Prod.mk.{0, 0} (@Nat) (@Nat) _v3 (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4) (@OfNat.ofNat.{0} (@Nat) (1 :
  Nat) (@instOfNatNat (1 : Nat)))))))),
(∀ (_v9 : (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.tagMatches (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v5 _v6))
  (@Bool.true))),
(∀ (_v10 : (@Pnp3.Models.Circuit _v3)),
(∀ (_v11 : (@List.{0} (@Bool))),
(∀ (_v12 : (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Pnp3.Models.Circuit _v3) (@List.{0} (@Bool))))
  (@Pnp4.Frontier.ContractExpansion.decodeCircuitFull _v3 (@Pnp4.Frontier.ContractExpansion.bitLength _v3)
  (@SerializedBody.window (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)
  (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v5 _v6) (@Cursor.Target.M _v0 _v3 _v4) (@Cursor.Target.W _v0 _v3)))
  (@Option.some.{0} (@Prod.{0, 0} (@Pnp3.Models.Circuit _v3) (@List.{0} (@Bool))) (@Prod.mk.{0, 0} (@Pnp3.Models.Circuit
  _v3) (@List.{0} (@Bool)) _v10 _v11)))),
(∀ (_v13 : (@LE.le.{0} (@Nat) (@instLENat) (@Pnp3.Models.Circuit.size _v3 _v10) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v3 _v0) _v0))),
(∀ (_v14 : (∀ (_v14 : (@Nat)),
(∀ (_v15 : (@LT.lt.{0} (@Nat) (@instLTNat) _v14 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat)
  (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v3))),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v5 _v6) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)) _v14))
  (@Pnp3.Models.Circuit.eval _v3 _v10 (@Pnp3.Core.vecOfNat _v3 _v14)))))),
(@Iff (@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v1 _v2
  _v5 _v6) (@Bool.true)) (@Exists.{(0 + 1)} (@Nat) (fun (_v15 : (@Nat)) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@Pnp4.Frontier.ContractExpansion.readNatBE (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v4)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v3))
  (@Pnp4.Frontier.ContractExpansion.bitLength (@Cursor.Target.W _v0 _v3))) (@Cursor.Target.W _v0 _v3))
  (@Pnp4.Frontier.ContractExpansion.padWord (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v5 _v6) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v4)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v3))
  (@Pnp4.Frontier.ContractExpansion.bitLength (@Cursor.Target.W _v0 _v3))) (@Cursor.Target.W _v0 _v3))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4))
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v3))
  (@Pnp4.Frontier.ContractExpansion.bitLength (@Cursor.Target.W _v0 _v3))) (@Option.some.{0} (@Nat) _v15)) (@And
  (@LE.le.{0} (@Nat) (@instLENat) _v15 (@Cursor.Target.W _v0 _v3)) (@And (∀ (_v16 : (@Nat)),
(∀ (_v17 : (@LT.lt.{0} (@Nat) (@instLTNat) _v16 _v15)),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v5 _v6) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 :
  Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))) _v4)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v3))
  (@Pnp4.Frontier.ContractExpansion.bitLength (@Cursor.Target.W _v0 _v3))) _v16))
  (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v5 _v6) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)) (@HPow.hPow.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid)))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v3)) (@Pnp4.Frontier.ContractExpansion.bitLength
  (@Cursor.Target.W _v0 _v3))) (@Cursor.Target.W _v0 _v3)) _v16))))) (∀ (_v16 : (@Nat)),
(∀ (_v17 : (@LE.le.{0} (@Nat) (@instLENat) _v15 _v16)),
(∀ (_v18 : (@LT.lt.{0} (@Nat) (@instLTNat) _v16 (@Cursor.Target.W _v0 _v3))),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v5 _v6) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 :
  Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))) _v4)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v3))
  (@Pnp4.Frontier.ContractExpansion.bitLength (@Cursor.Target.W _v0 _v3))) _v16)) (@Bool.false)))))))))))))))))))))))))) := by
  exact @NormalFinalClosure.rows_prefix_rho

-- Independent literal expected type for NormalFinalClosure.rows_prefix_rho_mirror.
noncomputable def PartACanonical.Types.p0541 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v6 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v2)),
(∀ (_v7 : (@Eq.{(0 + 1)} (@Nat) _v2 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v8 : (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Nat) (@Nat))) (@Pnp4.Frontier.ContractExpansion.contentHeader?
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2
  (@Bool) _v5 _v6)) (@Option.some.{0} (@Prod.{0, 0} (@Nat) (@Nat)) (@Prod.mk.{0, 0} (@Nat) (@Nat) _v3 (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4) (@OfNat.ofNat.{0} (@Nat) (1 :
  Nat) (@instOfNatNat (1 : Nat)))))))),
(∀ (_v9 : (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.tagMatches (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v5 _v6))
  (@Bool.true))),
(∀ (_v10 : (@Pnp3.Models.Circuit _v3)),
(∀ (_v11 : (@List.{0} (@Bool))),
(∀ (_v12 : (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Pnp3.Models.Circuit _v3) (@List.{0} (@Bool))))
  (@Pnp4.Frontier.ContractExpansion.decodeCircuitFull _v3 (@Pnp4.Frontier.ContractExpansion.bitLength _v3)
  (@SerializedBody.window (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)
  (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v5 _v6) (@Cursor.Target.M _v0 _v3 _v4) (@Cursor.Target.W _v0 _v3)))
  (@Option.some.{0} (@Prod.{0, 0} (@Pnp3.Models.Circuit _v3) (@List.{0} (@Bool))) (@Prod.mk.{0, 0} (@Pnp3.Models.Circuit
  _v3) (@List.{0} (@Bool)) _v10 _v11)))),
(∀ (_v13 : (@LE.le.{0} (@Nat) (@instLENat) (@Pnp3.Models.Circuit.size _v3 _v10) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v3 _v0) _v0))),
(∀ (_v14 : (∀ (_v14 : (@Nat)),
(∀ (_v15 : (@LT.lt.{0} (@Nat) (@instLTNat) _v14 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat)
  (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v3))),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v5 _v6) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)) _v14))
  (@Pnp3.Models.Circuit.eval _v3 _v10 (@Pnp3.Core.vecOfNat _v3 _v14)))))),
(@Iff (@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v1 _v2
  _v5 _v6) (@Bool.true)) (@Exists.{(0 + 1)} (@Nat) (fun (_v15 : (@Nat)) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@Pnp4.Frontier.ContractExpansion.readNatBE (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v4)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v3))
  (@Pnp4.Frontier.ContractExpansion.bitLength (@Cursor.Target.W _v0 _v3))) (@Cursor.Target.W _v0 _v3))
  (@Pnp4.Frontier.ContractExpansion.padWord (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v5 _v6) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v4)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v3))
  (@Pnp4.Frontier.ContractExpansion.bitLength (@Cursor.Target.W _v0 _v3))) (@Cursor.Target.W _v0 _v3))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4))
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v3))
  (@Pnp4.Frontier.ContractExpansion.bitLength (@Cursor.Target.W _v0 _v3))) (@Option.some.{0} (@Nat) _v15)) (@And
  (@LE.le.{0} (@Nat) (@instLENat) _v15 (@Cursor.Target.W _v0 _v3)) (@And (∀ (_v16 : (@Nat)),
(∀ (_v17 : (@LT.lt.{0} (@Nat) (@instLTNat) _v16 _v15)),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v5 _v6) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 :
  Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))) _v4)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v3))
  (@Pnp4.Frontier.ContractExpansion.bitLength (@Cursor.Target.W _v0 _v3))) _v16))
  (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v5 _v6) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)) (@HPow.hPow.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid)))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v3)) (@Pnp4.Frontier.ContractExpansion.bitLength
  (@Cursor.Target.W _v0 _v3))) (@Cursor.Target.W _v0 _v3)) _v16))))) (∀ (_v16 : (@Nat)),
(∀ (_v17 : (@LE.le.{0} (@Nat) (@instLENat) _v15 _v16)),
(∀ (_v18 : (@LT.lt.{0} (@Nat) (@instLTNat) _v16 (@Cursor.Target.W _v0 _v3))),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v5 _v6) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 :
  Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))) _v4)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v3))
  (@Pnp4.Frontier.ContractExpansion.bitLength (@Cursor.Target.W _v0 _v3))) _v16)) (@Bool.false)))))))))))))))))))))))))) := by
  exact @NormalFinalClosure.rows_prefix_rho_mirror

-- Complete literal proposition for NormalFinalClosure.rows_prefix_rho_mirror; original proof reused.
theorem PartACanonical.Surface.m0316 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v6 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v2)),
(∀ (_v7 : (@Eq.{(0 + 1)} (@Nat) _v2 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v8 : (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Nat) (@Nat))) (@Pnp4.Frontier.ContractExpansion.contentHeader?
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2
  (@Bool) _v5 _v6)) (@Option.some.{0} (@Prod.{0, 0} (@Nat) (@Nat)) (@Prod.mk.{0, 0} (@Nat) (@Nat) _v3 (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4) (@OfNat.ofNat.{0} (@Nat) (1 :
  Nat) (@instOfNatNat (1 : Nat)))))))),
(∀ (_v9 : (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.tagMatches (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v5 _v6))
  (@Bool.true))),
(∀ (_v10 : (@Pnp3.Models.Circuit _v3)),
(∀ (_v11 : (@List.{0} (@Bool))),
(∀ (_v12 : (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Pnp3.Models.Circuit _v3) (@List.{0} (@Bool))))
  (@Pnp4.Frontier.ContractExpansion.decodeCircuitFull _v3 (@Pnp4.Frontier.ContractExpansion.bitLength _v3)
  (@SerializedBody.window (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)
  (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v5 _v6) (@Cursor.Target.M _v0 _v3 _v4) (@Cursor.Target.W _v0 _v3)))
  (@Option.some.{0} (@Prod.{0, 0} (@Pnp3.Models.Circuit _v3) (@List.{0} (@Bool))) (@Prod.mk.{0, 0} (@Pnp3.Models.Circuit
  _v3) (@List.{0} (@Bool)) _v10 _v11)))),
(∀ (_v13 : (@LE.le.{0} (@Nat) (@instLENat) (@Pnp3.Models.Circuit.size _v3 _v10) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v3 _v0) _v0))),
(∀ (_v14 : (∀ (_v14 : (@Nat)),
(∀ (_v15 : (@LT.lt.{0} (@Nat) (@instLTNat) _v14 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat)
  (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v3))),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v5 _v6) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)) _v14))
  (@Pnp3.Models.Circuit.eval _v3 _v10 (@Pnp3.Core.vecOfNat _v3 _v14)))))),
(@Iff (@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v1 _v2
  _v5 _v6) (@Bool.true)) (@Exists.{(0 + 1)} (@Nat) (fun (_v15 : (@Nat)) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@Pnp4.Frontier.ContractExpansion.readNatBE (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v4)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v3))
  (@Pnp4.Frontier.ContractExpansion.bitLength (@Cursor.Target.W _v0 _v3))) (@Cursor.Target.W _v0 _v3))
  (@Pnp4.Frontier.ContractExpansion.padWord (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v5 _v6) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v4)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v3))
  (@Pnp4.Frontier.ContractExpansion.bitLength (@Cursor.Target.W _v0 _v3))) (@Cursor.Target.W _v0 _v3))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4))
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v3))
  (@Pnp4.Frontier.ContractExpansion.bitLength (@Cursor.Target.W _v0 _v3))) (@Option.some.{0} (@Nat) _v15)) (@And
  (@LE.le.{0} (@Nat) (@instLENat) _v15 (@Cursor.Target.W _v0 _v3)) (@And (∀ (_v16 : (@Nat)),
(∀ (_v17 : (@LT.lt.{0} (@Nat) (@instLTNat) _v16 _v15)),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v5 _v6) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 :
  Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))) _v4)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v3))
  (@Pnp4.Frontier.ContractExpansion.bitLength (@Cursor.Target.W _v0 _v3))) _v16))
  (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v5 _v6) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)) (@HPow.hPow.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid)))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v3)) (@Pnp4.Frontier.ContractExpansion.bitLength
  (@Cursor.Target.W _v0 _v3))) (@Cursor.Target.W _v0 _v3)) _v16))))) (∀ (_v16 : (@Nat)),
(∀ (_v17 : (@LE.le.{0} (@Nat) (@instLENat) _v15 _v16)),
(∀ (_v18 : (@LT.lt.{0} (@Nat) (@instLTNat) _v16 (@Cursor.Target.W _v0 _v3))),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v5 _v6) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 :
  Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))) _v4)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v3))
  (@Pnp4.Frontier.ContractExpansion.bitLength (@Cursor.Target.W _v0 _v3))) _v16)) (@Bool.false)))))))))))))))))))))))))) := by
  exact @NormalFinalClosure.rows_prefix_rho_mirror

-- Independent literal expected type for PhysicalCallerClosure.AmbientBody.
noncomputable def PartACanonical.Types.p0542 :
(Sort 0) := by
  exact @PhysicalCallerClosure.AmbientBody

-- Independent literal expected type for PhysicalCallerClosure.CallerRows.
noncomputable def PartACanonical.Types.p0543 :
(∀ (_v0 : (@Nat)),
(Sort 0)) := by
  exact @PhysicalCallerClosure.CallerRows

-- Independent literal expected type for PhysicalCallerClosure.InstalledBody.
noncomputable def PartACanonical.Types.p0544 :
(∀ (_v0 : (@Nat)),
(Sort 0)) := by
  exact @PhysicalCallerClosure.InstalledBody

-- Independent literal expected type for PhysicalCallerClosure.RawEntry.
noncomputable def PartACanonical.Types.p0545 :
(∀ (_v0 : (@Nat)),
(Sort 0)) := by
  exact @PhysicalCallerClosure.RawEntry

-- Independent literal expected type for PhysicalCallerClosure.RawFirst.
noncomputable def PartACanonical.Types.p0546 :
(∀ (_v0 : (@Nat)),
(Sort 0)) := by
  exact @PhysicalCallerClosure.RawFirst

-- Independent literal expected type for PhysicalCallerClosure.ambient_body.
noncomputable def PartACanonical.Types.p0547 :
(@PhysicalCallerClosure.AmbientBody) := by
  exact @PhysicalCallerClosure.ambient_body

-- Complete literal proposition for PhysicalCallerClosure.ambient_body; original proof reused.
theorem PartACanonical.Surface.m0317 :
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
(∀ (_v10 : (∀ (_v10 : (@Fin _v2)),
(@Bool))),
(∀ (_v11 : (∀ (_v11 : (@Fin _v4)),
(@Bool))),
(∀ (_v12 : (∀ (_v12 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v13 : (@LE.le.{0} (@Nat) (@instLENat) _v5 _v2)),
(∀ (_v14 : (@LE.le.{0} (@Nat) (@instLENat) _v2 _v1)),
(∀ (_v15 : (@LE.le.{0} (@Nat) (@instLENat) _v6 _v5)),
(∀ (_v16 : (@LE.le.{0} (@Nat) (@instLENat) _v7 _v5)),
(∀ (_v17 : (@LE.le.{0} (@Nat) (@instLENat) (@Pnp4.Frontier.ContractExpansion.bitLength _v4) _v5)),
(∀ (_v18 : (@LE.le.{0} (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v2 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) _v8 _v2)) _v5)),
(let _v19 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v3) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat))));
(let _v20 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v19 _v4) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat))));
(let _v21 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v1);
(∀ (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v9)),
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v20 _v9) _v21)),
(∀ (_v24 : (∀ (_v24 : (@Nat)),
(∀ (_v25 : (@LE.le.{0} (@Nat) (@instLENat) _v8 _v24)),
(∀ (_v26 : (@LT.lt.{0} (@Nat) (@instLTNat) _v24 _v2)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v12 _v24) (@Option.some.{0} (@Bool) (@_v10 (@Fin.mk _v2 _v24 _v26)))))))),
(∀ (_v25 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v12 _v2) (@Option.none.{0} (@Bool)))),
(∀ (_v26 : (∀ (_v26 : (@Nat)),
(∀ (_v27 : (@LT.lt.{0} (@Nat) (@instLTNat) _v2 _v26)),
(∀ (_v28 : (@LT.lt.{0} (@Nat) (@instLTNat) _v26 _v19)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v12 _v26) (@Option.some.{0} (@Bool) (@Bool.false))))))),
(∀ (_v27 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v12 _v19) (@Option.none.{0} (@Bool)))),
(∀ (_v28 : (∀ (_v28 : (@Fin _v4)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v12 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v20 (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Fin.val _v4 _v28))) (@Option.some.{0} (@Bool) (@_v11 _v28))))),
(∀ (_v29 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v12 _v20) (@Option.none.{0} (@Bool)))),
(∀ (_v30 : (∀ (_v30 : (@Nat)),
(∀ (_v31 : (@LT.lt.{0} (@Nat) (@instLTNat) _v20 _v30)),
(∀ (_v32 : (@LE.le.{0} (@Nat) (@instLENat) _v30 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v20 _v9))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v12 _v30) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v31 : (∀ (_v31 : (@Nat)),
(∀ (_v32 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v20 _v9) _v31)),
(∀ (_v33 : (@LT.lt.{0} (@Nat) (@instLTNat) _v31 _v21)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v12 _v31) (@Option.none.{0} (@Bool))))))),
(∀ (_v32 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v12 _v21) (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v33 : (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter _v21 _v5 _v4 (@OfNat.ofNat.{0} (@Nat) (12 : Nat)
  (@instOfNatNat (12 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v0))),
(∀ (_v34 : (@LT.lt.{0} (@Nat) (@instLTNat) _v20 (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v0))),
(let _v35 : (@List.{0} (@Bool)) := (@SerializedBody.window _v2 _v10 _v8 _v7);
(let _v36 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v1 _v0) := (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v1 _v0 (@SerializedBody.entry
  (@SerializedBody.sourceMode _v2 _v10 _v8)) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v0) _v20 _v34) (fun
  (_v36 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v0))) =>
(@SerializedBody.prepared _v12 _v2 _v8 _v21 _v5 _v4 _v6 _v7 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v0)
  _v36))));
(let _v37 : (@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool)))) := (@Bind.bind.{0, 0}
  (@Option.{0}) (@Monad.toBind.{0, 0} (@Option.{0}) (@instMonadOption.{0})) (@Prod.{0, 0} (@Pnp3.Models.Circuit _v4)
  (@List.{0} (@Bool))) (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool)))
  (@Pnp4.Frontier.ContractExpansion.decodeCircuitFull _v4 (@Pnp4.Frontier.ContractExpansion.bitLength _v4) _v35) (fun
  (_v37 : (@Prod.{0, 0} (@Pnp3.Models.Circuit _v4) (@List.{0} (@Bool)))) =>
(@PhysicalCallerClosure.AmbientBody.match_1.{(0 + 1)} _v4 (fun (_v38 : (@Prod.{0, 0} (@Pnp3.Models.Circuit _v4)
  (@List.{0} (@Bool)))) =>
(@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool))))) _v37 (fun (_v38 : (@Pnp3.Models.Circuit
  _v4)) =>
(fun (_v39 : (@List.{0} (@Bool))) =>
(@ite.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool)))) (@LE.le.{0} (@Nat)
  (@instLENat) (@Pnp3.Models.Circuit.size _v4 _v38) _v6) (@Nat.decLe (@Pnp3.Models.Circuit.size _v4 _v38) _v6)
  (@Option.some.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool))) (@Prod.mk.{0, 0} (@Prod.{0, 0} (@Nat)
  (@Bool)) (@List.{0} (@Bool)) (@Prod.mk.{0, 0} (@Nat) (@Bool) (@Pnp3.Models.Circuit.size _v4 _v38)
  (@Pnp3.Models.Circuit.eval _v4 _v38 _v11)) _v39)) (@Option.none.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool))
  (@List.{0} (@Bool))))))))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v38 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v38 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (1073741824 : Nat) (@instOfNatNat (1073741824 : Nat))) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))) (@And (∀ (_v39 : (@Nat)),
(∀ (_v40 : (@LE.le.{0} (@Nat) (@instLENat) _v39 _v38)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))
  _v1 _v0 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v1 _v0 _v39 _v36))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@SerializedBody.machine))))) (@And (∀ (_v39 : (@Nat)),
(∀ (_v40 : (@LT.lt.{0} (@Nat) (@instLTNat) _v39 _v38)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))
  _v1 _v0 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v1 _v0 _v39 _v36))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@SerializedBody.machine))) (@And (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v1 _v0
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v1 _v0 _v39 _v36)) (@SerializedBody.done
  (@Bool.false))) (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))
  _v1 _v0 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v1 _v0 _v39 _v36)) (@SerializedBody.done
  (@Bool.true))))))) (@PhysicalCallerClosure.AmbientBody.match_3.{(0 + 1)} (fun (_v39 : (@Option.{0} (@Prod.{0, 0}
  (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool))))) =>
(Sort 0)) _v37 (fun (_v39 : (@Unit)) =>
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v1 _v0) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v1 _v0 _v38
  _v36) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v1 _v0 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@SerializedBody.machine)) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v0) _v20 _v34) (fun (_v40 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v1 _v0))) =>
(@SerializedBody.image _v12 _v21 _v5 _v4 _v6 _v7 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v2 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) _v8 _v2)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 :
  Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v0) _v40)))))) (fun (_v39 : (@Nat)) =>
(fun (_v40 : (@Bool)) =>
(fun (_v41 : (@List.{0} (@Bool))) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v42 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v42 _v7) (@And (@Eq.{(0 + 1)} (@List.{0} (@Bool)) _v41 (@List.drop.{0} (@Bool)
  _v42 _v35)) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v1 _v0) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v1 _v0 _v38
  _v36) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v1 _v0 (@SerializedBody.done _v40) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v0)
  _v20 _v34) (fun (_v43 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v0))) =>
(@SerializedBody.image _v12 _v21 _v5 _v4 _v6 _v7 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v2 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) _v8 _v2)) _v39 _v42 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v7 _v42) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v0) _v43)))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @PhysicalCallerClosure.ambient_body

-- Independent literal expected type for PhysicalCallerClosure.ambient_body_mirror.
noncomputable def PartACanonical.Types.p0548 :
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
(∀ (_v10 : (∀ (_v10 : (@Fin _v2)),
(@Bool))),
(∀ (_v11 : (∀ (_v11 : (@Fin _v4)),
(@Bool))),
(∀ (_v12 : (∀ (_v12 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v13 : (@LE.le.{0} (@Nat) (@instLENat) _v5 _v2)),
(∀ (_v14 : (@LE.le.{0} (@Nat) (@instLENat) _v2 _v1)),
(∀ (_v15 : (@LE.le.{0} (@Nat) (@instLENat) _v6 _v5)),
(∀ (_v16 : (@LE.le.{0} (@Nat) (@instLENat) _v7 _v5)),
(∀ (_v17 : (@LE.le.{0} (@Nat) (@instLENat) (@Pnp4.Frontier.ContractExpansion.bitLength _v4) _v5)),
(∀ (_v18 : (@LE.le.{0} (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v2 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) _v8 _v2)) _v5)),
(let _v19 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v3) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat))));
(let _v20 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v19 _v4) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat))));
(let _v21 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v1);
(∀ (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v9)),
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v20 _v9) _v21)),
(∀ (_v24 : (∀ (_v24 : (@Nat)),
(∀ (_v25 : (@LE.le.{0} (@Nat) (@instLENat) _v8 _v24)),
(∀ (_v26 : (@LT.lt.{0} (@Nat) (@instLTNat) _v24 _v2)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v12 _v24) (@Option.some.{0} (@Bool) (@_v10 (@Fin.mk _v2 _v24 _v26)))))))),
(∀ (_v25 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v12 _v2) (@Option.none.{0} (@Bool)))),
(∀ (_v26 : (∀ (_v26 : (@Nat)),
(∀ (_v27 : (@LT.lt.{0} (@Nat) (@instLTNat) _v2 _v26)),
(∀ (_v28 : (@LT.lt.{0} (@Nat) (@instLTNat) _v26 _v19)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v12 _v26) (@Option.some.{0} (@Bool) (@Bool.false))))))),
(∀ (_v27 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v12 _v19) (@Option.none.{0} (@Bool)))),
(∀ (_v28 : (∀ (_v28 : (@Fin _v4)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v12 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v20 (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Fin.val _v4 _v28))) (@Option.some.{0} (@Bool) (@_v11 _v28))))),
(∀ (_v29 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v12 _v20) (@Option.none.{0} (@Bool)))),
(∀ (_v30 : (∀ (_v30 : (@Nat)),
(∀ (_v31 : (@LT.lt.{0} (@Nat) (@instLTNat) _v20 _v30)),
(∀ (_v32 : (@LE.le.{0} (@Nat) (@instLENat) _v30 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v20 _v9))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v12 _v30) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v31 : (∀ (_v31 : (@Nat)),
(∀ (_v32 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v20 _v9) _v31)),
(∀ (_v33 : (@LT.lt.{0} (@Nat) (@instLTNat) _v31 _v21)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v12 _v31) (@Option.none.{0} (@Bool))))))),
(∀ (_v32 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v12 _v21) (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v33 : (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter _v21 _v5 _v4 (@OfNat.ofNat.{0} (@Nat) (12 : Nat)
  (@instOfNatNat (12 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v0))),
(∀ (_v34 : (@LT.lt.{0} (@Nat) (@instLTNat) _v20 (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v0))),
(let _v35 : (@List.{0} (@Bool)) := (@SerializedBody.window _v2 _v10 _v8 _v7);
(let _v36 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v1 _v0) := (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v1 _v0 (@SerializedBody.entry
  (@SerializedBody.sourceMode _v2 _v10 _v8)) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v0) _v20 _v34) (fun
  (_v36 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v0))) =>
(@SerializedBody.prepared _v12 _v2 _v8 _v21 _v5 _v4 _v6 _v7 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v0)
  _v36))));
(let _v37 : (@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool)))) := (@Bind.bind.{0, 0}
  (@Option.{0}) (@Monad.toBind.{0, 0} (@Option.{0}) (@instMonadOption.{0})) (@Prod.{0, 0} (@Pnp3.Models.Circuit _v4)
  (@List.{0} (@Bool))) (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool)))
  (@Pnp4.Frontier.ContractExpansion.decodeCircuitFull _v4 (@Pnp4.Frontier.ContractExpansion.bitLength _v4) _v35) (fun
  (_v37 : (@Prod.{0, 0} (@Pnp3.Models.Circuit _v4) (@List.{0} (@Bool)))) =>
(@PhysicalCallerClosure.ambient_body_mirror.match_1.{(0 + 1)} _v4 (fun (_v38 : (@Prod.{0, 0} (@Pnp3.Models.Circuit _v4)
  (@List.{0} (@Bool)))) =>
(@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool))))) _v37 (fun (_v38 : (@Pnp3.Models.Circuit
  _v4)) =>
(fun (_v39 : (@List.{0} (@Bool))) =>
(@ite.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool)))) (@LE.le.{0} (@Nat)
  (@instLENat) (@Pnp3.Models.Circuit.size _v4 _v38) _v6) (@Nat.decLe (@Pnp3.Models.Circuit.size _v4 _v38) _v6)
  (@Option.some.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool))) (@Prod.mk.{0, 0} (@Prod.{0, 0} (@Nat)
  (@Bool)) (@List.{0} (@Bool)) (@Prod.mk.{0, 0} (@Nat) (@Bool) (@Pnp3.Models.Circuit.size _v4 _v38)
  (@Pnp3.Models.Circuit.eval _v4 _v38 _v11)) _v39)) (@Option.none.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool))
  (@List.{0} (@Bool))))))))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v38 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v38 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (1073741824 : Nat) (@instOfNatNat (1073741824 : Nat))) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))) (@And (∀ (_v39 : (@Nat)),
(∀ (_v40 : (@LE.le.{0} (@Nat) (@instLENat) _v39 _v38)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))
  _v1 _v0 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v1 _v0 _v39 _v36))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@SerializedBody.machine))))) (@And (∀ (_v39 : (@Nat)),
(∀ (_v40 : (@LT.lt.{0} (@Nat) (@instLTNat) _v39 _v38)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))
  _v1 _v0 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v1 _v0 _v39 _v36))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@SerializedBody.machine))) (@And (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v1 _v0
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v1 _v0 _v39 _v36)) (@SerializedBody.done
  (@Bool.false))) (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))
  _v1 _v0 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v1 _v0 _v39 _v36)) (@SerializedBody.done
  (@Bool.true))))))) (@PhysicalCallerClosure.ambient_body_mirror.match_3.{(0 + 1)} (fun (_v39 : (@Option.{0} (@Prod.{0, 0}
  (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool))))) =>
(Sort 0)) _v37 (fun (_v39 : (@Unit)) =>
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v1 _v0) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v1 _v0 _v38
  _v36) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v1 _v0 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@SerializedBody.machine)) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v0) _v20 _v34) (fun (_v40 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v1 _v0))) =>
(@SerializedBody.image _v12 _v21 _v5 _v4 _v6 _v7 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v2 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) _v8 _v2)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 :
  Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v0) _v40)))))) (fun (_v39 : (@Nat)) =>
(fun (_v40 : (@Bool)) =>
(fun (_v41 : (@List.{0} (@Bool))) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v42 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v42 _v7) (@And (@Eq.{(0 + 1)} (@List.{0} (@Bool)) _v41 (@List.drop.{0} (@Bool)
  _v42 _v35)) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v1 _v0) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v1 _v0 _v38
  _v36) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v1 _v0 (@SerializedBody.done _v40) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v0)
  _v20 _v34) (fun (_v43 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v0))) =>
(@SerializedBody.image _v12 _v21 _v5 _v4 _v6 _v7 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v2 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) _v8 _v2)) _v39 _v42 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v7 _v42) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v0) _v43)))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @PhysicalCallerClosure.ambient_body_mirror

-- Complete literal proposition for PhysicalCallerClosure.ambient_body_mirror; original proof reused.
theorem PartACanonical.Surface.m0318 :
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
(∀ (_v10 : (∀ (_v10 : (@Fin _v2)),
(@Bool))),
(∀ (_v11 : (∀ (_v11 : (@Fin _v4)),
(@Bool))),
(∀ (_v12 : (∀ (_v12 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v13 : (@LE.le.{0} (@Nat) (@instLENat) _v5 _v2)),
(∀ (_v14 : (@LE.le.{0} (@Nat) (@instLENat) _v2 _v1)),
(∀ (_v15 : (@LE.le.{0} (@Nat) (@instLENat) _v6 _v5)),
(∀ (_v16 : (@LE.le.{0} (@Nat) (@instLENat) _v7 _v5)),
(∀ (_v17 : (@LE.le.{0} (@Nat) (@instLENat) (@Pnp4.Frontier.ContractExpansion.bitLength _v4) _v5)),
(∀ (_v18 : (@LE.le.{0} (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v2 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) _v8 _v2)) _v5)),
(let _v19 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v3) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat))));
(let _v20 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v19 _v4) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat))));
(let _v21 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v1);
(∀ (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v9)),
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v20 _v9) _v21)),
(∀ (_v24 : (∀ (_v24 : (@Nat)),
(∀ (_v25 : (@LE.le.{0} (@Nat) (@instLENat) _v8 _v24)),
(∀ (_v26 : (@LT.lt.{0} (@Nat) (@instLTNat) _v24 _v2)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v12 _v24) (@Option.some.{0} (@Bool) (@_v10 (@Fin.mk _v2 _v24 _v26)))))))),
(∀ (_v25 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v12 _v2) (@Option.none.{0} (@Bool)))),
(∀ (_v26 : (∀ (_v26 : (@Nat)),
(∀ (_v27 : (@LT.lt.{0} (@Nat) (@instLTNat) _v2 _v26)),
(∀ (_v28 : (@LT.lt.{0} (@Nat) (@instLTNat) _v26 _v19)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v12 _v26) (@Option.some.{0} (@Bool) (@Bool.false))))))),
(∀ (_v27 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v12 _v19) (@Option.none.{0} (@Bool)))),
(∀ (_v28 : (∀ (_v28 : (@Fin _v4)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v12 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v20 (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Fin.val _v4 _v28))) (@Option.some.{0} (@Bool) (@_v11 _v28))))),
(∀ (_v29 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v12 _v20) (@Option.none.{0} (@Bool)))),
(∀ (_v30 : (∀ (_v30 : (@Nat)),
(∀ (_v31 : (@LT.lt.{0} (@Nat) (@instLTNat) _v20 _v30)),
(∀ (_v32 : (@LE.le.{0} (@Nat) (@instLENat) _v30 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v20 _v9))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v12 _v30) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v31 : (∀ (_v31 : (@Nat)),
(∀ (_v32 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v20 _v9) _v31)),
(∀ (_v33 : (@LT.lt.{0} (@Nat) (@instLTNat) _v31 _v21)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v12 _v31) (@Option.none.{0} (@Bool))))))),
(∀ (_v32 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v12 _v21) (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v33 : (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter _v21 _v5 _v4 (@OfNat.ofNat.{0} (@Nat) (12 : Nat)
  (@instOfNatNat (12 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v0))),
(∀ (_v34 : (@LT.lt.{0} (@Nat) (@instLTNat) _v20 (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v0))),
(let _v35 : (@List.{0} (@Bool)) := (@SerializedBody.window _v2 _v10 _v8 _v7);
(let _v36 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v1 _v0) := (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v1 _v0 (@SerializedBody.entry
  (@SerializedBody.sourceMode _v2 _v10 _v8)) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v0) _v20 _v34) (fun
  (_v36 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v0))) =>
(@SerializedBody.prepared _v12 _v2 _v8 _v21 _v5 _v4 _v6 _v7 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v0)
  _v36))));
(let _v37 : (@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool)))) := (@Bind.bind.{0, 0}
  (@Option.{0}) (@Monad.toBind.{0, 0} (@Option.{0}) (@instMonadOption.{0})) (@Prod.{0, 0} (@Pnp3.Models.Circuit _v4)
  (@List.{0} (@Bool))) (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool)))
  (@Pnp4.Frontier.ContractExpansion.decodeCircuitFull _v4 (@Pnp4.Frontier.ContractExpansion.bitLength _v4) _v35) (fun
  (_v37 : (@Prod.{0, 0} (@Pnp3.Models.Circuit _v4) (@List.{0} (@Bool)))) =>
(@PhysicalCallerClosure.ambient_body_mirror.match_1.{(0 + 1)} _v4 (fun (_v38 : (@Prod.{0, 0} (@Pnp3.Models.Circuit _v4)
  (@List.{0} (@Bool)))) =>
(@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool))))) _v37 (fun (_v38 : (@Pnp3.Models.Circuit
  _v4)) =>
(fun (_v39 : (@List.{0} (@Bool))) =>
(@ite.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool)))) (@LE.le.{0} (@Nat)
  (@instLENat) (@Pnp3.Models.Circuit.size _v4 _v38) _v6) (@Nat.decLe (@Pnp3.Models.Circuit.size _v4 _v38) _v6)
  (@Option.some.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool))) (@Prod.mk.{0, 0} (@Prod.{0, 0} (@Nat)
  (@Bool)) (@List.{0} (@Bool)) (@Prod.mk.{0, 0} (@Nat) (@Bool) (@Pnp3.Models.Circuit.size _v4 _v38)
  (@Pnp3.Models.Circuit.eval _v4 _v38 _v11)) _v39)) (@Option.none.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool))
  (@List.{0} (@Bool))))))))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v38 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v38 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (1073741824 : Nat) (@instOfNatNat (1073741824 : Nat))) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))) (@And (∀ (_v39 : (@Nat)),
(∀ (_v40 : (@LE.le.{0} (@Nat) (@instLENat) _v39 _v38)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))
  _v1 _v0 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v1 _v0 _v39 _v36))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@SerializedBody.machine))))) (@And (∀ (_v39 : (@Nat)),
(∀ (_v40 : (@LT.lt.{0} (@Nat) (@instLTNat) _v39 _v38)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))
  _v1 _v0 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v1 _v0 _v39 _v36))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@SerializedBody.machine))) (@And (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v1 _v0
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v1 _v0 _v39 _v36)) (@SerializedBody.done
  (@Bool.false))) (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))
  _v1 _v0 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v1 _v0 _v39 _v36)) (@SerializedBody.done
  (@Bool.true))))))) (@PhysicalCallerClosure.ambient_body_mirror.match_3.{(0 + 1)} (fun (_v39 : (@Option.{0} (@Prod.{0, 0}
  (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool))))) =>
(Sort 0)) _v37 (fun (_v39 : (@Unit)) =>
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v1 _v0) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v1 _v0 _v38
  _v36) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v1 _v0 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@SerializedBody.machine)) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v0) _v20 _v34) (fun (_v40 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v1 _v0))) =>
(@SerializedBody.image _v12 _v21 _v5 _v4 _v6 _v7 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v2 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) _v8 _v2)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 :
  Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v0) _v40)))))) (fun (_v39 : (@Nat)) =>
(fun (_v40 : (@Bool)) =>
(fun (_v41 : (@List.{0} (@Bool))) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v42 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v42 _v7) (@And (@Eq.{(0 + 1)} (@List.{0} (@Bool)) _v41 (@List.drop.{0} (@Bool)
  _v42 _v35)) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v1 _v0) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v1 _v0 _v38
  _v36) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v1 _v0 (@SerializedBody.done _v40) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v0)
  _v20 _v34) (fun (_v43 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v0))) =>
(@SerializedBody.image _v12 _v21 _v5 _v4 _v6 _v7 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v2 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) _v8 _v2)) _v39 _v42 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v7 _v42) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v0) _v43)))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @PhysicalCallerClosure.ambient_body_mirror

-- Independent literal expected type for PhysicalCallerClosure.body_run.
noncomputable def PartACanonical.Types.p0549 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v1 _v2)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@BodyIngress.machine _v0)) _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@BodyIngress.machine _v0) _v1 _v2 _v3
  (@BodyIngress.bodyConfig _v0 _v1 _v2 _v4)) (@BodyIngress.bodyConfig _v0 _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v1 _v2 _v3 _v4)))))))) := by
  exact @PhysicalCallerClosure.body_run

-- Complete literal proposition for PhysicalCallerClosure.body_run; original proof reused.
theorem PartACanonical.Surface.m0319 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v1 _v2)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@BodyIngress.machine _v0)) _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@BodyIngress.machine _v0) _v1 _v2 _v3
  (@BodyIngress.bodyConfig _v0 _v1 _v2 _v4)) (@BodyIngress.bodyConfig _v0 _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v1 _v2 _v3 _v4)))))))) := by
  exact @PhysicalCallerClosure.body_run

-- Independent literal expected type for PhysicalCallerClosure.body_run_mirror.
noncomputable def PartACanonical.Types.p0550 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v1 _v2)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@BodyIngress.machine _v0)) _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@BodyIngress.machine _v0) _v1 _v2 _v3
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)) _v1
  _v2 (@BodyIngress.body _v0 (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v1 _v2 _v4)) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v1 _v2 _v4)
  (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))
  _v1 _v2 _v4))) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@BodyIngress.machine _v0)) _v1 _v2 (@BodyIngress.body _v0 (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v1 _v2 _v3 _v4)))
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))
  _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v1 _v2 _v3 _v4))
  (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))
  _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v1 _v2 _v3 _v4))))))))) := by
  exact @PhysicalCallerClosure.body_run_mirror

-- Complete literal proposition for PhysicalCallerClosure.body_run_mirror; original proof reused.
theorem PartACanonical.Surface.m0320 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v1 _v2)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@BodyIngress.machine _v0)) _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@BodyIngress.machine _v0) _v1 _v2 _v3
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)) _v1
  _v2 (@BodyIngress.body _v0 (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v1 _v2 _v4)) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v1 _v2 _v4)
  (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))
  _v1 _v2 _v4))) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@BodyIngress.machine _v0)) _v1 _v2 (@BodyIngress.body _v0 (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v1 _v2 _v3 _v4)))
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))
  _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v1 _v2 _v3 _v4))
  (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))
  _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v1 _v2 _v3 _v4))))))))) := by
  exact @PhysicalCallerClosure.body_run_mirror

-- Independent literal expected type for PhysicalCallerClosure.callerImage.
noncomputable def PartACanonical.Types.p0551 :
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
(∀ (_v10 : (∀ (_v10 : (@Fin _v3)),
(@Bool))),
(∀ (_v11 : (@Nat)),
(∀ (_v12 : (@Nat)),
(∀ (_v13 : (@Nat)),
(∀ (_v14 : (@Nat)),
(∀ (_v15 : (@Nat)),
(@Option.{0} (@Bool)))))))))))))))))) := by
  exact @PhysicalCallerClosure.callerImage

-- Independent literal expected type for PhysicalCallerClosure.callerMachine.
noncomputable def PartACanonical.Types.p0552 :
(∀ (_v0 : (@Nat)),
(@Pnp3.Complexity.Uniform.V1.UniformTM)) := by
  exact @PhysicalCallerClosure.callerMachine

-- Independent literal expected type for PhysicalCallerClosure.caller_prefix.
noncomputable def PartACanonical.Types.p0553 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ {_v3 : (@Nat)},
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine
  _v0)) _v1 _v2)),
(∀ (_v5 : (∀ (_v5 : (@Nat)),
(∀ (_v6 : (@LT.lt.{0} (@Nat) (@instLTNat) _v5 _v3)),
(∀ (_v7 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@BodyIngress.machine _v0) _v1 _v2 _v5 _v4)) (@BodyIngress.body _v0
  (@SerializedBody.entry _v7))))))),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@LE.le.{0} (@Nat) (@instLENat) _v6 _v3)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v1 _v2 _v6 (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v1 _v2
  (@PhysicalCallerClosure.oldState _v0 (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)) _v1 _v2 _v4))
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  _v1 _v2 _v4) (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@BodyIngress.machine _v0)) _v1 _v2 _v4))) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v1 _v2
  (@PhysicalCallerClosure.oldState _v0 (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)) _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@BodyIngress.machine _v0) _v1 _v2 _v6 _v4)))
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@BodyIngress.machine _v0) _v1 _v2 _v6 _v4))
  (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@BodyIngress.machine _v0) _v1 _v2 _v6 _v4)))))))))))) := by
  exact @PhysicalCallerClosure.caller_prefix

-- Complete literal proposition for PhysicalCallerClosure.caller_prefix; original proof reused.
theorem PartACanonical.Surface.m0321 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ {_v3 : (@Nat)},
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine
  _v0)) _v1 _v2)),
(∀ (_v5 : (∀ (_v5 : (@Nat)),
(∀ (_v6 : (@LT.lt.{0} (@Nat) (@instLTNat) _v5 _v3)),
(∀ (_v7 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@BodyIngress.machine _v0) _v1 _v2 _v5 _v4)) (@BodyIngress.body _v0
  (@SerializedBody.entry _v7))))))),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@LE.le.{0} (@Nat) (@instLENat) _v6 _v3)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v1 _v2 _v6 (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v1 _v2
  (@PhysicalCallerClosure.oldState _v0 (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)) _v1 _v2 _v4))
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  _v1 _v2 _v4) (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@BodyIngress.machine _v0)) _v1 _v2 _v4))) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v1 _v2
  (@PhysicalCallerClosure.oldState _v0 (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)) _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@BodyIngress.machine _v0) _v1 _v2 _v6 _v4)))
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@BodyIngress.machine _v0) _v1 _v2 _v6 _v4))
  (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@BodyIngress.machine _v0) _v1 _v2 _v6 _v4)))))))))))) := by
  exact @PhysicalCallerClosure.caller_prefix

-- Independent literal expected type for PhysicalCallerClosure.caller_prefix_mirror.
noncomputable def PartACanonical.Types.p0554 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ {_v3 : (@Nat)},
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine
  _v0)) _v1 _v2)),
(∀ (_v5 : (∀ (_v5 : (@Nat)),
(∀ (_v6 : (@LT.lt.{0} (@Nat) (@instLTNat) _v5 _v3)),
(∀ (_v7 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@BodyIngress.machine _v0) _v1 _v2 _v5 _v4)) (@BodyIngress.body _v0
  (@SerializedBody.entry _v7))))))),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@LE.le.{0} (@Nat) (@instLENat) _v6 _v3)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v1 _v2 _v6 (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v1 _v2
  (@PhysicalCallerClosure.oldState _v0 (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)) _v1 _v2 _v4))
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  _v1 _v2 _v4) (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@BodyIngress.machine _v0)) _v1 _v2 _v4))) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v1 _v2
  (@PhysicalCallerClosure.oldState _v0 (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)) _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@BodyIngress.machine _v0) _v1 _v2 _v6 _v4)))
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@BodyIngress.machine _v0) _v1 _v2 _v6 _v4))
  (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@BodyIngress.machine _v0) _v1 _v2 _v6 _v4)))))))))))) := by
  exact @PhysicalCallerClosure.caller_prefix_mirror

-- Complete literal proposition for PhysicalCallerClosure.caller_prefix_mirror; original proof reused.
theorem PartACanonical.Surface.m0322 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ {_v3 : (@Nat)},
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine
  _v0)) _v1 _v2)),
(∀ (_v5 : (∀ (_v5 : (@Nat)),
(∀ (_v6 : (@LT.lt.{0} (@Nat) (@instLTNat) _v5 _v3)),
(∀ (_v7 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@BodyIngress.machine _v0) _v1 _v2 _v5 _v4)) (@BodyIngress.body _v0
  (@SerializedBody.entry _v7))))))),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@LE.le.{0} (@Nat) (@instLENat) _v6 _v3)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v1 _v2 _v6 (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v1 _v2
  (@PhysicalCallerClosure.oldState _v0 (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)) _v1 _v2 _v4))
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  _v1 _v2 _v4) (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@BodyIngress.machine _v0)) _v1 _v2 _v4))) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v1 _v2
  (@PhysicalCallerClosure.oldState _v0 (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)) _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@BodyIngress.machine _v0) _v1 _v2 _v6 _v4)))
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@BodyIngress.machine _v0) _v1 _v2 _v6 _v4))
  (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@BodyIngress.machine _v0) _v1 _v2 _v6 _v4)))))))))))) := by
  exact @PhysicalCallerClosure.caller_prefix_mirror

-- Independent literal expected type for PhysicalCallerClosure.caller_raw_entry.
noncomputable def PartACanonical.Types.p0555 :
(∀ (_v0 : (@Nat)),
(@PhysicalCallerClosure.RawEntry _v0)) := by
  exact @PhysicalCallerClosure.caller_raw_entry

-- Complete literal proposition for PhysicalCallerClosure.caller_raw_entry; original proof reused.
theorem PartACanonical.Surface.m0323 :
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
(let _v25 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11)) := (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v9 _v7) _v12) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) _v8);
(∀ (_v26 : (@LT.lt.{0} (@Nat) (@instLTNat) _v15 _v9)),
(∀ (_v27 : (@LE.le.{0} (@Nat) (@instLENat) (@Pnp4.Frontier.ContractExpansion.bitLength _v12) _v16)),
(∀ (_v28 : (@LE.le.{0} (@Nat) (@instLENat) _v17 _v16)),
(@Exists.{(0 + 1)} (@Nat) (fun (_v29 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v29 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (17179869184 : Nat) (@instOfNatNat (17179869184 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))) (@And (@Eq.{(0 + 1)}
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@PhysicalCallerClosure.callerMachine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v29 (@Pnp3.Complexity.Uniform.V1.initialConfig
  (@PhysicalCallerClosure.callerMachine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4))) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@PhysicalCallerClosure.oldState _v0
  (@BodyIngress.body _v0 (@SerializedBody.entry (@SerializedBody.sourceMode (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v3 _v4) _v18)))) _v25 (fun (_v30 :
  (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11))) =>
(@SerializedBody.prepared _v24 _v9 _v18 _v14 _v16 _v12 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) _v12 _v0) _v0) _v17 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11) _v30))))) (@And (∀ (_v30 : (@Nat)),
(∀ (_v31 : (@LT.lt.{0} (@Nat) (@instLTNat) _v30 _v29)),
(∀ (_v32 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@PhysicalCallerClosure.callerMachine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v30 (@Pnp3.Complexity.Uniform.V1.initialConfig
  (@PhysicalCallerClosure.callerMachine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4)))) (@PhysicalCallerClosure.oldState _v0
  (@BodyIngress.body _v0 (@SerializedBody.entry _v32))))))) (∀ (_v30 : (@Nat)),
(∀ (_v31 : (@LE.le.{0} (@Nat) (@instLENat) _v30 _v29)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine
  _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@PhysicalCallerClosure.callerMachine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v30 (@Pnp3.Complexity.Uniform.V1.initialConfig
  (@PhysicalCallerClosure.callerMachine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept
  (@PhysicalCallerClosure.callerMachine _v0))) (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v30
  (@Pnp3.Complexity.Uniform.V1.initialConfig (@PhysicalCallerClosure.callerMachine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair
  _v1 _v2 _v3 _v4)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@PhysicalCallerClosure.callerMachine
  _v0))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @PhysicalCallerClosure.caller_raw_entry

-- Independent literal expected type for PhysicalCallerClosure.caller_rows.
noncomputable def PartACanonical.Types.p0556 :
(∀ (_v0 : (@Nat)),
(@PhysicalCallerClosure.CallerRows _v0)) := by
  exact @PhysicalCallerClosure.caller_rows

-- Complete literal proposition for PhysicalCallerClosure.caller_rows; original proof reused.
theorem PartACanonical.Surface.m0324 :
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
(∀ (_v14 : (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) _v2)),
(∀ (_v15 : (@LE.le.{0} (@Nat) (@instLENat) _v6 _v3)),
(∀ (_v16 : (@LE.le.{0} (@Nat) (@instLENat) _v3 _v2)),
(∀ (_v17 : (@LE.le.{0} (@Nat) (@instLENat) _v7 _v6)),
(∀ (_v18 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v8)),
(∀ (_v19 : (@LE.le.{0} (@Nat) (@instLENat) _v8 _v6)),
(∀ (_v20 : (@LE.le.{0} (@Nat) (@instLENat) (@Pnp4.Frontier.ContractExpansion.bitLength _v5) _v6)),
(∀ (_v21 : (@LE.le.{0} (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v3 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) _v9 _v3)) _v6)),
(∀ (_v22 : (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v10)),
(∀ (_v23 : (@LE.le.{0} (@Nat) (@instLENat) _v10 _v3)),
(∀ (_v24 : (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 (@HPow.hPow.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid)))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v5)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))) _v9)),
(let _v25 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat))));
(let _v26 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v25 _v5) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat))));
(let _v27 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v2);
(∀ (_v28 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v11)),
(∀ (_v29 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v26 _v11) _v27)),
(∀ (_v30 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))) (@Option.none.{0} (@Bool)))),
(∀ (_v31 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Option.some.{0} (@Bool)
  (@Bool.true)))),
(∀ (_v32 : (∀ (_v32 : (@Nat)),
(∀ (_v33 : (@LE.le.{0} (@Nat) (@instLENat) _v10 _v32)),
(∀ (_v34 : (@LT.lt.{0} (@Nat) (@instLTNat) _v32 _v3)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 _v32) (@Option.some.{0} (@Bool) (@_v12 (@Fin.mk _v3 _v32 _v34)))))))),
(∀ (_v33 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 _v3) (@Option.none.{0} (@Bool)))),
(∀ (_v34 : (∀ (_v34 : (@Nat)),
(∀ (_v35 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v34)),
(∀ (_v36 : (@LT.lt.{0} (@Nat) (@instLTNat) _v34 _v25)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 _v34) (@Option.some.{0} (@Bool) (@Bool.false))))))),
(∀ (_v35 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 _v25) (@Option.none.{0} (@Bool)))),
(∀ (_v36 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 _v26) (@Option.none.{0} (@Bool)))),
(∀ (_v37 : (∀ (_v37 : (@Fin _v5)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v26 (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Fin.val _v5 _v37))) (@Option.some.{0} (@Bool) (@Bool.false))))),
(∀ (_v38 : (∀ (_v38 : (@Nat)),
(∀ (_v39 : (@LT.lt.{0} (@Nat) (@instLTNat) _v26 _v38)),
(∀ (_v40 : (@LE.le.{0} (@Nat) (@instLENat) _v38 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v26 _v11))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 _v38) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v39 : (∀ (_v39 : (@Nat)),
(∀ (_v40 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v26 _v11) _v39)),
(∀ (_v41 : (@LT.lt.{0} (@Nat) (@instLTNat) _v39 _v27)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 _v39) (@Option.none.{0} (@Bool))))))),
(∀ (_v40 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 _v27) (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v41 : (∀ (_v41 : (@Nat)),
(∀ (_v42 : (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter _v27 _v6 _v5 (@OfNat.ofNat.{0} (@Nat) (12 : Nat)
  (@instOfNatNat (12 : Nat)))) _v41)),
(∀ (_v43 : (@LE.le.{0} (@Nat) (@instLENat) _v41 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@SerializedBody.delimiter _v27 _v6 _v5 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 _v41) (@Option.none.{0} (@Bool))))))),
(∀ (_v42 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@SerializedBody.delimiter _v27 _v6 _v5 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1))),
(∀ (_v43 : (@LT.lt.{0} (@Nat) (@instLTNat) _v26 (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1))),
(let _v44 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1) := (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1
  (@PhysicalCallerClosure.oldState _v0 (@BodyIngress.body _v0 (@SerializedBody.entry (@SerializedBody.sourceMode _v3 _v12
  _v9)))) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v26 _v43) (fun (_v44 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1))) =>
(@SerializedBody.prepared _v13 _v3 _v9 _v27 _v6 _v5 _v7 _v8 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1)
  _v44))));
(let _v45 : (@List.{0} (@Bool)) := (@SerializedBody.window _v3 _v12 _v9 _v8);
(@Exists.{(0 + 1)} (@Nat) (fun (_v46 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v46 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (1099511627776 : Nat) (@instOfNatNat (1099511627776 : Nat))) (@HPow.hPow.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))))) (@And (∀ (_v47 : (@Nat)),
(∀ (_v48 : (@LE.le.{0} (@Nat) (@instLENat) _v47 _v46)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v2 _v1 _v47 _v44)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept
  (@PhysicalCallerClosure.callerMachine _v0))))) (@And (∀ (_v47 : (@Nat)),
(∀ (_v48 : (@LT.lt.{0} (@Nat) (@instLTNat) _v47 _v46)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine
  _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v2 _v1 _v47 _v44)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject
  (@PhysicalCallerClosure.callerMachine _v0))) (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@PhysicalCallerClosure.callerMachine _v0) _v2 _v1 _v47 _v44))
  (@PhysicalCallerClosure.rowsDone _v0))))) (@PhysicalCallerClosure.CallerRows.match_1.{(0 + 1)} _v5 (fun (_v47 :
  (@Option.{0} (@Prod.{0, 0} (@Pnp3.Models.Circuit _v5) (@List.{0} (@Bool))))) =>
(Sort 0)) (@Pnp4.Frontier.ContractExpansion.decodeCircuitFull _v5 (@Pnp4.Frontier.ContractExpansion.bitLength _v5) _v45)
  (fun (_v47 : (@Unit)) =>
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v2 _v1 _v46 _v44) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@PhysicalCallerClosure.callerMachine _v0)) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v26 _v43) (fun (_v48 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v2 _v1))) =>
(@PhysicalCallerClosure.callerImage _v13 _v3 _v4 _v5 _v27 _v6 _v7 _v8 _v9 _v11 (@Pnp3.Core.vecOfNat _v5
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v48)))))) (fun (_v47 : (@Pnp3.Models.Circuit _v5)) =>
(fun (_v48 : (@List.{0} (@Bool))) =>
(@Or (@And (@Not (@LE.le.{0} (@Nat) (@instLENat) (@Pnp3.Models.Circuit.size _v5 _v47) _v7)) (@Eq.{(0 + 1)}
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v2 _v1 _v46 _v44) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@PhysicalCallerClosure.callerMachine _v0)) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v26 _v43) (fun (_v49 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v2 _v1))) =>
(@PhysicalCallerClosure.callerImage _v13 _v3 _v4 _v5 _v27 _v6 _v7 _v8 _v9 _v11 (@Pnp3.Core.vecOfNat _v5
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v49)))))) (@And (@LE.le.{0} (@Nat) (@instLENat)
  (@Pnp3.Models.Circuit.size _v5 _v47) _v7) (let _v49 : (@Nat) := (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHSub.{0} (@Nat) (@instSubNat)) _v8 (@List.length.{0} (@Bool) _v48));
(let _v50 : (∀ (_v50 : (@Nat)),
(Sort 0)) := (fun (_v50 : (@Nat)) =>
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead _v3 _v12 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 _v50)) (@Pnp3.Models.Circuit.eval _v5 _v47 (@Pnp3.Core.vecOfNat _v5 _v50))));
(@And (@LE.le.{0} (@Nat) (@instLENat) _v49 _v8) (@And (@Eq.{(0 + 1)} (@List.{0} (@Bool)) _v48 (@List.drop.{0} (@Bool)
  _v49 _v45)) (@And (@Exists.{(0 + 1)} (∀ (_v51 : (@Fin (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v5) _v11))),
(@Nat)) (fun (_v51 : (∀ (_v51 : (@Fin (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))) _v5) _v11))),
(@Nat))) =>
(@And (∀ (_v52 : (@Fin (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v5) _v11))),
(∀ (_v53 : (∀ (_v53 : (@Nat)),
(∀ (_v54 : (@LT.lt.{0} (@Nat) (@instLTNat) _v53 (@Fin.val (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid)))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v5) _v11) _v52))),
(@_v50 _v53)))),
(@And (@LT.lt.{0} (@Nat) (@instLTNat) (@_v51 _v52) _v46) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@PhysicalCallerClosure.callerMachine _v0) _v2 _v1 (@_v51 _v52) _v44)
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1 (@PhysicalCallerClosure.evalState _v0 (@SerializedBody.entry
  (@SerializedBody.sourceMode _v3 _v12 _v9))) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v26 _v43) (fun
  (_v54 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1))) =>
(@PartACanonical.PrivateABI.a0028 _v13 _v3 _v4 _v5 _v27 _v6 _v7 _v8 _v9 _v10 _v11 (@Fin.val (@Min.min.{0} (@Nat)
  (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0}
  (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v5) _v11) _v52) _v12 (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v54)))))))) (∀ (_v52 : (@Fin (@Min.min.{0} (@Nat)
  (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0}
  (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v5) _v11))),
(∀ (_v53 : (@Fin (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0,
  0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))) _v5) _v11))),
(∀ (_v54 : (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v5) _v11) _v52) (@Fin.val (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib)
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v5) _v11) _v53))),
(∀ (_v55 : (∀ (_v55 : (@Nat)),
(∀ (_v56 : (@LT.lt.{0} (@Nat) (@instLTNat) _v55 (@Fin.val (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid)))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v5) _v11) _v53))),
(@_v50 _v55)))),
(@LT.lt.{0} (@Nat) (@instLTNat) (@_v51 _v52) (@_v51 _v53))))))))) (@Or (@And (@LE.le.{0} (@Nat) (@instLENat)
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v5) _v11) (@And (∀ (_v51 : (@Nat)),
(∀ (_v52 : (@LT.lt.{0} (@Nat) (@instLTNat) _v51 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat)
  (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v5))),
(@_v50 _v51))) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v2 _v1 _v46 _v44) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1
  (@PhysicalCallerClosure.rowsDone _v0) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v26 _v43) (fun (_v51 :
  (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1))) =>
(@PhysicalCallerClosure.callerImage _v13 _v3 _v4 _v5 _v27 _v6 _v7 _v8 _v9 (@Max.max.{0} (@Nat) (@Nat.instMax_mathlib)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0}
  (@Nat) (@instSubNat)) _v11 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v5)))
  (@Pnp3.Core.vecOfNat _v5 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Pnp3.Models.Circuit.size _v5
  _v47) _v49 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v8 _v49) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v51))))))) (@Or
  (@Exists.{(0 + 1)} (@Nat) (fun (_v51 : (@Nat)) =>
(@And (@LT.lt.{0} (@Nat) (@instLTNat) _v51 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v5) _v11)) (@And (∀ (_v52 : (@Nat)),
(∀ (_v53 : (@LT.lt.{0} (@Nat) (@instLTNat) _v52 _v51)),
(@_v50 _v52))) (@And (@Not (@_v50 _v51)) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@PhysicalCallerClosure.callerMachine _v0) _v2 _v1 _v46 _v44)
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject
  (@PhysicalCallerClosure.callerMachine _v0)) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v26 _v43) (fun
  (_v52 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1))) =>
(@PhysicalCallerClosure.callerImage _v13 _v3 _v4 _v5 _v27 _v6 _v7 _v8 _v9 (@Max.max.{0} (@Nat) (@Nat.instMax_mathlib)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0}
  (@Nat) (@instSubNat)) _v11 _v51)) (@Pnp3.Core.vecOfNat _v5 _v51) (@Pnp3.Models.Circuit.size _v5 _v47) _v49
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v8 _v49) (@OfNat.ofNat.{0} (@Nat) (0 :
  Nat) (@instOfNatNat (0 : Nat))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v52)))))))))) (@And
  (@LT.lt.{0} (@Nat) (@instLTNat) _v11 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v5))
  (@And (∀ (_v51 : (@Nat)),
(∀ (_v52 : (@LT.lt.{0} (@Nat) (@instLTNat) _v51 _v11)),
(@_v50 _v51))) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v2 _v1 _v46 _v44) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@PhysicalCallerClosure.callerMachine _v0)) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v26 _v43) (fun (_v51 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v2 _v1))) =>
(@PhysicalCallerClosure.callerImage _v13 _v3 _v4 _v5 _v27 _v6 _v7 _v8 _v9 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))) (@Pnp3.Core.vecOfNat _v5 _v11) (@Pnp3.Models.Circuit.size _v5 _v47) _v49 (@HSub.hSub.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v8 _v49) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1)
  _v51)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @PhysicalCallerClosure.caller_rows

-- Independent literal expected type for PhysicalCallerClosure.caller_rows_mirror.
noncomputable def PartACanonical.Types.p0557 :
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
(∀ (_v14 : (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) _v2)),
(∀ (_v15 : (@LE.le.{0} (@Nat) (@instLENat) _v6 _v3)),
(∀ (_v16 : (@LE.le.{0} (@Nat) (@instLENat) _v3 _v2)),
(∀ (_v17 : (@LE.le.{0} (@Nat) (@instLENat) _v7 _v6)),
(∀ (_v18 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v8)),
(∀ (_v19 : (@LE.le.{0} (@Nat) (@instLENat) _v8 _v6)),
(∀ (_v20 : (@LE.le.{0} (@Nat) (@instLENat) (@Pnp4.Frontier.ContractExpansion.bitLength _v5) _v6)),
(∀ (_v21 : (@LE.le.{0} (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v3 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) _v9 _v3)) _v6)),
(∀ (_v22 : (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v10)),
(∀ (_v23 : (@LE.le.{0} (@Nat) (@instLENat) _v10 _v3)),
(∀ (_v24 : (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 (@HPow.hPow.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid)))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v5)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))) _v9)),
(let _v25 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat))));
(let _v26 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v25 _v5) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat))));
(let _v27 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v2);
(∀ (_v28 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v11)),
(∀ (_v29 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v26 _v11) _v27)),
(∀ (_v30 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))) (@Option.none.{0} (@Bool)))),
(∀ (_v31 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Option.some.{0} (@Bool)
  (@Bool.true)))),
(∀ (_v32 : (∀ (_v32 : (@Nat)),
(∀ (_v33 : (@LE.le.{0} (@Nat) (@instLENat) _v10 _v32)),
(∀ (_v34 : (@LT.lt.{0} (@Nat) (@instLTNat) _v32 _v3)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 _v32) (@Option.some.{0} (@Bool) (@_v12 (@Fin.mk _v3 _v32 _v34)))))))),
(∀ (_v33 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 _v3) (@Option.none.{0} (@Bool)))),
(∀ (_v34 : (∀ (_v34 : (@Nat)),
(∀ (_v35 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v34)),
(∀ (_v36 : (@LT.lt.{0} (@Nat) (@instLTNat) _v34 _v25)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 _v34) (@Option.some.{0} (@Bool) (@Bool.false))))))),
(∀ (_v35 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 _v25) (@Option.none.{0} (@Bool)))),
(∀ (_v36 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 _v26) (@Option.none.{0} (@Bool)))),
(∀ (_v37 : (∀ (_v37 : (@Fin _v5)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v26 (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Fin.val _v5 _v37))) (@Option.some.{0} (@Bool) (@Bool.false))))),
(∀ (_v38 : (∀ (_v38 : (@Nat)),
(∀ (_v39 : (@LT.lt.{0} (@Nat) (@instLTNat) _v26 _v38)),
(∀ (_v40 : (@LE.le.{0} (@Nat) (@instLENat) _v38 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v26 _v11))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 _v38) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v39 : (∀ (_v39 : (@Nat)),
(∀ (_v40 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v26 _v11) _v39)),
(∀ (_v41 : (@LT.lt.{0} (@Nat) (@instLTNat) _v39 _v27)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 _v39) (@Option.none.{0} (@Bool))))))),
(∀ (_v40 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 _v27) (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v41 : (∀ (_v41 : (@Nat)),
(∀ (_v42 : (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter _v27 _v6 _v5 (@OfNat.ofNat.{0} (@Nat) (12 : Nat)
  (@instOfNatNat (12 : Nat)))) _v41)),
(∀ (_v43 : (@LE.le.{0} (@Nat) (@instLENat) _v41 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@SerializedBody.delimiter _v27 _v6 _v5 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 _v41) (@Option.none.{0} (@Bool))))))),
(∀ (_v42 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@SerializedBody.delimiter _v27 _v6 _v5 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1))),
(∀ (_v43 : (@LT.lt.{0} (@Nat) (@instLTNat) _v26 (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1))),
(let _v44 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1) := (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1
  (@PhysicalCallerClosure.oldState _v0 (@BodyIngress.body _v0 (@SerializedBody.entry (@SerializedBody.sourceMode _v3 _v12
  _v9)))) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v26 _v43) (fun (_v44 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1))) =>
(@SerializedBody.prepared _v13 _v3 _v9 _v27 _v6 _v5 _v7 _v8 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1)
  _v44))));
(let _v45 : (@List.{0} (@Bool)) := (@SerializedBody.window _v3 _v12 _v9 _v8);
(@Exists.{(0 + 1)} (@Nat) (fun (_v46 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v46 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (1099511627776 : Nat) (@instOfNatNat (1099511627776 : Nat))) (@HPow.hPow.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))))) (@And (∀ (_v47 : (@Nat)),
(∀ (_v48 : (@LE.le.{0} (@Nat) (@instLENat) _v47 _v46)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v2 _v1 _v47 _v44)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept
  (@PhysicalCallerClosure.callerMachine _v0))))) (@And (∀ (_v47 : (@Nat)),
(∀ (_v48 : (@LT.lt.{0} (@Nat) (@instLTNat) _v47 _v46)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine
  _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v2 _v1 _v47 _v44)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject
  (@PhysicalCallerClosure.callerMachine _v0))) (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@PhysicalCallerClosure.callerMachine _v0) _v2 _v1 _v47 _v44))
  (@PhysicalCallerClosure.rowsDone _v0))))) (@PhysicalCallerClosure.caller_rows_mirror.match_1.{(0 + 1)} _v5 (fun (_v47 :
  (@Option.{0} (@Prod.{0, 0} (@Pnp3.Models.Circuit _v5) (@List.{0} (@Bool))))) =>
(Sort 0)) (@Pnp4.Frontier.ContractExpansion.decodeCircuitFull _v5 (@Pnp4.Frontier.ContractExpansion.bitLength _v5) _v45)
  (fun (_v47 : (@Unit)) =>
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v2 _v1 _v46 _v44) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@PhysicalCallerClosure.callerMachine _v0)) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v26 _v43) (fun (_v48 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v2 _v1))) =>
(@PhysicalCallerClosure.callerImage _v13 _v3 _v4 _v5 _v27 _v6 _v7 _v8 _v9 _v11 (@Pnp3.Core.vecOfNat _v5
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v48)))))) (fun (_v47 : (@Pnp3.Models.Circuit _v5)) =>
(fun (_v48 : (@List.{0} (@Bool))) =>
(@Or (@And (@Not (@LE.le.{0} (@Nat) (@instLENat) (@Pnp3.Models.Circuit.size _v5 _v47) _v7)) (@Eq.{(0 + 1)}
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v2 _v1 _v46 _v44) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@PhysicalCallerClosure.callerMachine _v0)) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v26 _v43) (fun (_v49 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v2 _v1))) =>
(@PhysicalCallerClosure.callerImage _v13 _v3 _v4 _v5 _v27 _v6 _v7 _v8 _v9 _v11 (@Pnp3.Core.vecOfNat _v5
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v49)))))) (@And (@LE.le.{0} (@Nat) (@instLENat)
  (@Pnp3.Models.Circuit.size _v5 _v47) _v7) (let _v49 : (@Nat) := (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHSub.{0} (@Nat) (@instSubNat)) _v8 (@List.length.{0} (@Bool) _v48));
(let _v50 : (∀ (_v50 : (@Nat)),
(Sort 0)) := (fun (_v50 : (@Nat)) =>
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead _v3 _v12 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 _v50)) (@Pnp3.Models.Circuit.eval _v5 _v47 (@Pnp3.Core.vecOfNat _v5 _v50))));
(@And (@LE.le.{0} (@Nat) (@instLENat) _v49 _v8) (@And (@Eq.{(0 + 1)} (@List.{0} (@Bool)) _v48 (@List.drop.{0} (@Bool)
  _v49 _v45)) (@And (@Exists.{(0 + 1)} (∀ (_v51 : (@Fin (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v5) _v11))),
(@Nat)) (fun (_v51 : (∀ (_v51 : (@Fin (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))) _v5) _v11))),
(@Nat))) =>
(@And (∀ (_v52 : (@Fin (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v5) _v11))),
(∀ (_v53 : (∀ (_v53 : (@Nat)),
(∀ (_v54 : (@LT.lt.{0} (@Nat) (@instLTNat) _v53 (@Fin.val (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid)))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v5) _v11) _v52))),
(@_v50 _v53)))),
(@And (@LT.lt.{0} (@Nat) (@instLTNat) (@_v51 _v52) _v46) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@PhysicalCallerClosure.callerMachine _v0) _v2 _v1 (@_v51 _v52) _v44)
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1 (@PhysicalCallerClosure.evalState _v0 (@SerializedBody.entry
  (@SerializedBody.sourceMode _v3 _v12 _v9))) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v26 _v43) (fun
  (_v54 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1))) =>
(let _v55 : (@Nat) := (@SerializedBody.delimiter _v27 _v6 _v5 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 :
  Nat))));
(let _v56 : (@Bool) := (@Decidable.decide (@LE.le.{0} (@Nat) (@instLENat) _v3 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 (@Fin.val (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v5) _v11) _v52))) (@Nat.decLe _v3 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 (@Fin.val (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid)))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v5) _v11) _v52))));
(let _v57 : (@Bool) := (@Pnp4.Frontier.ContractExpansion.padRead _v3 _v12 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 (@Fin.val (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v5) _v11) _v52)));
(let _v58 : (@Bool) := (@Decidable.decide (@LE.le.{0} (@Nat) (@instLENat) _v3 _v9) (@Nat.decLe _v3 _v9));
(let _v59 : (@Bool) := (@Pnp4.Frontier.ContractExpansion.padRead _v3 _v12 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHSub.{0} (@Nat) (@instSubNat)) _v9 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))));
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1)
  _v54) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v55 (@OfNat.ofNat.{0} (@Nat) (1 :
  Nat) (@instOfNatNat (1 : Nat))))) (@instDecidableEqNat (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v54)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v55 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@Option.some.{0} (@Bool) _v56) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat)
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v54) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v55 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))
  (@instDecidableEqNat (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v54) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v55 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))
  (@Option.some.{0} (@Bool) _v57) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v54) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v55 (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))) (@instDecidableEqNat (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v54) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v55 (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))) (@Option.some.{0} (@Bool) _v58)
  (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1)
  _v54) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v55 (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat))))) (@instDecidableEqNat (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v54)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v55 (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))))) (@Option.some.{0} (@Bool) (@ite.{(0 + 1)} (@Bool) (@LT.lt.{0} (@Nat) (@instLTNat) _v9 _v3)
  (@Nat.decLt _v9 _v3) _v59 (@Bool.false))) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v54) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v55 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))) (@instDecidableEqNat (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v54) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v55 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))) (@Option.some.{0} (@Bool)
  (@Bool.false)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@Eq.{(0 + 1)} (@Nat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v54) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v10 (@Fin.val (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v5) _v11) _v52))) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v54) _v3)) (@instDecidableAnd (@Eq.{(0 + 1)} (@Nat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v54) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v10 (@Fin.val (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v5) _v11) _v52))) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v54) _v3) (@instDecidableEqNat (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v54) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v10 (@Fin.val (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v5) _v11) _v52))) (@Nat.decLt (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1)
  _v54) _v3)) (@Option.none.{0} (@Bool)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v9
  _v3) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v54) (@HSub.hSub.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v9 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))
  (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) _v9 _v3) (@Eq.{(0 + 1)} (@Nat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v54) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v9 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Nat.decLt _v9 _v3)
  (@instDecidableEqNat (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v54) (@HSub.hSub.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v9 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))
  (@Option.none.{0} (@Bool)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@Eq.{(0 + 1)} (@Nat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v54) _v9) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v54) _v3)) (@instDecidableAnd (@Eq.{(0 + 1)} (@Nat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v54) _v9) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v54) _v3) (@instDecidableEqNat (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v54) _v9) (@Nat.decLt (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v54) _v3)) (@Option.none.{0} (@Bool))
  (@PhysicalCallerClosure.callerImage _v13 _v3 _v4 _v5 _v27 _v6 _v7 _v8 _v9 (@Max.max.{0} (@Nat) (@Nat.instMax_mathlib)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0}
  (@Nat) (@instSubNat)) _v11 (@Fin.val (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))) _v5) _v11) _v52))) (@Pnp3.Core.vecOfNat _v5 (@Fin.val (@Min.min.{0} (@Nat)
  (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0}
  (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v5) _v11) _v52))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) _v8 _v7 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v54))))))))))))))))))))) (∀ (_v52 : (@Fin
  (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v5)
  _v11))),
(∀ (_v53 : (@Fin (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0,
  0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))) _v5) _v11))),
(∀ (_v54 : (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v5) _v11) _v52) (@Fin.val (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib)
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v5) _v11) _v53))),
(∀ (_v55 : (∀ (_v55 : (@Nat)),
(∀ (_v56 : (@LT.lt.{0} (@Nat) (@instLTNat) _v55 (@Fin.val (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid)))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v5) _v11) _v53))),
(@_v50 _v55)))),
(@LT.lt.{0} (@Nat) (@instLTNat) (@_v51 _v52) (@_v51 _v53))))))))) (@Or (@And (@LE.le.{0} (@Nat) (@instLENat)
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v5) _v11) (@And (∀ (_v51 : (@Nat)),
(∀ (_v52 : (@LT.lt.{0} (@Nat) (@instLTNat) _v51 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat)
  (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v5))),
(@_v50 _v51))) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v2 _v1 _v46 _v44) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1
  (@PhysicalCallerClosure.rowsDone _v0) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v26 _v43) (fun (_v51 :
  (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1))) =>
(@PhysicalCallerClosure.callerImage _v13 _v3 _v4 _v5 _v27 _v6 _v7 _v8 _v9 (@Max.max.{0} (@Nat) (@Nat.instMax_mathlib)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0}
  (@Nat) (@instSubNat)) _v11 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v5)))
  (@Pnp3.Core.vecOfNat _v5 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Pnp3.Models.Circuit.size _v5
  _v47) _v49 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v8 _v49) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v51))))))) (@Or
  (@Exists.{(0 + 1)} (@Nat) (fun (_v51 : (@Nat)) =>
(@And (@LT.lt.{0} (@Nat) (@instLTNat) _v51 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v5) _v11)) (@And (∀ (_v52 : (@Nat)),
(∀ (_v53 : (@LT.lt.{0} (@Nat) (@instLTNat) _v52 _v51)),
(@_v50 _v52))) (@And (@Not (@_v50 _v51)) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@PhysicalCallerClosure.callerMachine _v0) _v2 _v1 _v46 _v44)
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject
  (@PhysicalCallerClosure.callerMachine _v0)) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v26 _v43) (fun
  (_v52 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1))) =>
(@PhysicalCallerClosure.callerImage _v13 _v3 _v4 _v5 _v27 _v6 _v7 _v8 _v9 (@Max.max.{0} (@Nat) (@Nat.instMax_mathlib)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0}
  (@Nat) (@instSubNat)) _v11 _v51)) (@Pnp3.Core.vecOfNat _v5 _v51) (@Pnp3.Models.Circuit.size _v5 _v47) _v49
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v8 _v49) (@OfNat.ofNat.{0} (@Nat) (0 :
  Nat) (@instOfNatNat (0 : Nat))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v52)))))))))) (@And
  (@LT.lt.{0} (@Nat) (@instLTNat) _v11 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v5))
  (@And (∀ (_v51 : (@Nat)),
(∀ (_v52 : (@LT.lt.{0} (@Nat) (@instLTNat) _v51 _v11)),
(@_v50 _v51))) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v2 _v1 _v46 _v44) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@PhysicalCallerClosure.callerMachine _v0)) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v26 _v43) (fun (_v51 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v2 _v1))) =>
(@PhysicalCallerClosure.callerImage _v13 _v3 _v4 _v5 _v27 _v6 _v7 _v8 _v9 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))) (@Pnp3.Core.vecOfNat _v5 _v11) (@Pnp3.Models.Circuit.size _v5 _v47) _v49 (@HSub.hSub.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v8 _v49) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1)
  _v51)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @PhysicalCallerClosure.caller_rows_mirror

-- Complete literal proposition for PhysicalCallerClosure.caller_rows_mirror; original proof reused.
theorem PartACanonical.Surface.m0325 :
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
(∀ (_v14 : (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) _v2)),
(∀ (_v15 : (@LE.le.{0} (@Nat) (@instLENat) _v6 _v3)),
(∀ (_v16 : (@LE.le.{0} (@Nat) (@instLENat) _v3 _v2)),
(∀ (_v17 : (@LE.le.{0} (@Nat) (@instLENat) _v7 _v6)),
(∀ (_v18 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v8)),
(∀ (_v19 : (@LE.le.{0} (@Nat) (@instLENat) _v8 _v6)),
(∀ (_v20 : (@LE.le.{0} (@Nat) (@instLENat) (@Pnp4.Frontier.ContractExpansion.bitLength _v5) _v6)),
(∀ (_v21 : (@LE.le.{0} (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v3 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) _v9 _v3)) _v6)),
(∀ (_v22 : (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v10)),
(∀ (_v23 : (@LE.le.{0} (@Nat) (@instLENat) _v10 _v3)),
(∀ (_v24 : (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 (@HPow.hPow.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid)))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v5)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))) _v9)),
(let _v25 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat))));
(let _v26 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v25 _v5) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat))));
(let _v27 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v2);
(∀ (_v28 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v11)),
(∀ (_v29 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v26 _v11) _v27)),
(∀ (_v30 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))) (@Option.none.{0} (@Bool)))),
(∀ (_v31 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Option.some.{0} (@Bool)
  (@Bool.true)))),
(∀ (_v32 : (∀ (_v32 : (@Nat)),
(∀ (_v33 : (@LE.le.{0} (@Nat) (@instLENat) _v10 _v32)),
(∀ (_v34 : (@LT.lt.{0} (@Nat) (@instLTNat) _v32 _v3)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 _v32) (@Option.some.{0} (@Bool) (@_v12 (@Fin.mk _v3 _v32 _v34)))))))),
(∀ (_v33 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 _v3) (@Option.none.{0} (@Bool)))),
(∀ (_v34 : (∀ (_v34 : (@Nat)),
(∀ (_v35 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v34)),
(∀ (_v36 : (@LT.lt.{0} (@Nat) (@instLTNat) _v34 _v25)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 _v34) (@Option.some.{0} (@Bool) (@Bool.false))))))),
(∀ (_v35 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 _v25) (@Option.none.{0} (@Bool)))),
(∀ (_v36 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 _v26) (@Option.none.{0} (@Bool)))),
(∀ (_v37 : (∀ (_v37 : (@Fin _v5)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v26 (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Fin.val _v5 _v37))) (@Option.some.{0} (@Bool) (@Bool.false))))),
(∀ (_v38 : (∀ (_v38 : (@Nat)),
(∀ (_v39 : (@LT.lt.{0} (@Nat) (@instLTNat) _v26 _v38)),
(∀ (_v40 : (@LE.le.{0} (@Nat) (@instLENat) _v38 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v26 _v11))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 _v38) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v39 : (∀ (_v39 : (@Nat)),
(∀ (_v40 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v26 _v11) _v39)),
(∀ (_v41 : (@LT.lt.{0} (@Nat) (@instLTNat) _v39 _v27)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 _v39) (@Option.none.{0} (@Bool))))))),
(∀ (_v40 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 _v27) (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v41 : (∀ (_v41 : (@Nat)),
(∀ (_v42 : (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter _v27 _v6 _v5 (@OfNat.ofNat.{0} (@Nat) (12 : Nat)
  (@instOfNatNat (12 : Nat)))) _v41)),
(∀ (_v43 : (@LE.le.{0} (@Nat) (@instLENat) _v41 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@SerializedBody.delimiter _v27 _v6 _v5 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 _v41) (@Option.none.{0} (@Bool))))))),
(∀ (_v42 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@SerializedBody.delimiter _v27 _v6 _v5 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1))),
(∀ (_v43 : (@LT.lt.{0} (@Nat) (@instLTNat) _v26 (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1))),
(let _v44 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1) := (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1
  (@PhysicalCallerClosure.oldState _v0 (@BodyIngress.body _v0 (@SerializedBody.entry (@SerializedBody.sourceMode _v3 _v12
  _v9)))) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v26 _v43) (fun (_v44 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1))) =>
(@SerializedBody.prepared _v13 _v3 _v9 _v27 _v6 _v5 _v7 _v8 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1)
  _v44))));
(let _v45 : (@List.{0} (@Bool)) := (@SerializedBody.window _v3 _v12 _v9 _v8);
(@Exists.{(0 + 1)} (@Nat) (fun (_v46 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v46 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (1099511627776 : Nat) (@instOfNatNat (1099511627776 : Nat))) (@HPow.hPow.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))))) (@And (∀ (_v47 : (@Nat)),
(∀ (_v48 : (@LE.le.{0} (@Nat) (@instLENat) _v47 _v46)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v2 _v1 _v47 _v44)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept
  (@PhysicalCallerClosure.callerMachine _v0))))) (@And (∀ (_v47 : (@Nat)),
(∀ (_v48 : (@LT.lt.{0} (@Nat) (@instLTNat) _v47 _v46)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine
  _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v2 _v1 _v47 _v44)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject
  (@PhysicalCallerClosure.callerMachine _v0))) (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@PhysicalCallerClosure.callerMachine _v0) _v2 _v1 _v47 _v44))
  (@PhysicalCallerClosure.rowsDone _v0))))) (@PhysicalCallerClosure.caller_rows_mirror.match_1.{(0 + 1)} _v5 (fun (_v47 :
  (@Option.{0} (@Prod.{0, 0} (@Pnp3.Models.Circuit _v5) (@List.{0} (@Bool))))) =>
(Sort 0)) (@Pnp4.Frontier.ContractExpansion.decodeCircuitFull _v5 (@Pnp4.Frontier.ContractExpansion.bitLength _v5) _v45)
  (fun (_v47 : (@Unit)) =>
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v2 _v1 _v46 _v44) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@PhysicalCallerClosure.callerMachine _v0)) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v26 _v43) (fun (_v48 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v2 _v1))) =>
(@PhysicalCallerClosure.callerImage _v13 _v3 _v4 _v5 _v27 _v6 _v7 _v8 _v9 _v11 (@Pnp3.Core.vecOfNat _v5
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v48)))))) (fun (_v47 : (@Pnp3.Models.Circuit _v5)) =>
(fun (_v48 : (@List.{0} (@Bool))) =>
(@Or (@And (@Not (@LE.le.{0} (@Nat) (@instLENat) (@Pnp3.Models.Circuit.size _v5 _v47) _v7)) (@Eq.{(0 + 1)}
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v2 _v1 _v46 _v44) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@PhysicalCallerClosure.callerMachine _v0)) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v26 _v43) (fun (_v49 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v2 _v1))) =>
(@PhysicalCallerClosure.callerImage _v13 _v3 _v4 _v5 _v27 _v6 _v7 _v8 _v9 _v11 (@Pnp3.Core.vecOfNat _v5
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v49)))))) (@And (@LE.le.{0} (@Nat) (@instLENat)
  (@Pnp3.Models.Circuit.size _v5 _v47) _v7) (let _v49 : (@Nat) := (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHSub.{0} (@Nat) (@instSubNat)) _v8 (@List.length.{0} (@Bool) _v48));
(let _v50 : (∀ (_v50 : (@Nat)),
(Sort 0)) := (fun (_v50 : (@Nat)) =>
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead _v3 _v12 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 _v50)) (@Pnp3.Models.Circuit.eval _v5 _v47 (@Pnp3.Core.vecOfNat _v5 _v50))));
(@And (@LE.le.{0} (@Nat) (@instLENat) _v49 _v8) (@And (@Eq.{(0 + 1)} (@List.{0} (@Bool)) _v48 (@List.drop.{0} (@Bool)
  _v49 _v45)) (@And (@Exists.{(0 + 1)} (∀ (_v51 : (@Fin (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v5) _v11))),
(@Nat)) (fun (_v51 : (∀ (_v51 : (@Fin (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))) _v5) _v11))),
(@Nat))) =>
(@And (∀ (_v52 : (@Fin (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v5) _v11))),
(∀ (_v53 : (∀ (_v53 : (@Nat)),
(∀ (_v54 : (@LT.lt.{0} (@Nat) (@instLTNat) _v53 (@Fin.val (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid)))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v5) _v11) _v52))),
(@_v50 _v53)))),
(@And (@LT.lt.{0} (@Nat) (@instLTNat) (@_v51 _v52) _v46) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@PhysicalCallerClosure.callerMachine _v0) _v2 _v1 (@_v51 _v52) _v44)
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1 (@PhysicalCallerClosure.evalState _v0 (@SerializedBody.entry
  (@SerializedBody.sourceMode _v3 _v12 _v9))) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v26 _v43) (fun
  (_v54 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1))) =>
(let _v55 : (@Nat) := (@SerializedBody.delimiter _v27 _v6 _v5 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 :
  Nat))));
(let _v56 : (@Bool) := (@Decidable.decide (@LE.le.{0} (@Nat) (@instLENat) _v3 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 (@Fin.val (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v5) _v11) _v52))) (@Nat.decLe _v3 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 (@Fin.val (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid)))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v5) _v11) _v52))));
(let _v57 : (@Bool) := (@Pnp4.Frontier.ContractExpansion.padRead _v3 _v12 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 (@Fin.val (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v5) _v11) _v52)));
(let _v58 : (@Bool) := (@Decidable.decide (@LE.le.{0} (@Nat) (@instLENat) _v3 _v9) (@Nat.decLe _v3 _v9));
(let _v59 : (@Bool) := (@Pnp4.Frontier.ContractExpansion.padRead _v3 _v12 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHSub.{0} (@Nat) (@instSubNat)) _v9 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))));
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1)
  _v54) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v55 (@OfNat.ofNat.{0} (@Nat) (1 :
  Nat) (@instOfNatNat (1 : Nat))))) (@instDecidableEqNat (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v54)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v55 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@Option.some.{0} (@Bool) _v56) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat)
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v54) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v55 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))
  (@instDecidableEqNat (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v54) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v55 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))
  (@Option.some.{0} (@Bool) _v57) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v54) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v55 (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))) (@instDecidableEqNat (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v54) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v55 (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))) (@Option.some.{0} (@Bool) _v58)
  (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1)
  _v54) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v55 (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat))))) (@instDecidableEqNat (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v54)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v55 (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))))) (@Option.some.{0} (@Bool) (@ite.{(0 + 1)} (@Bool) (@LT.lt.{0} (@Nat) (@instLTNat) _v9 _v3)
  (@Nat.decLt _v9 _v3) _v59 (@Bool.false))) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v54) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v55 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))) (@instDecidableEqNat (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v54) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v55 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))) (@Option.some.{0} (@Bool)
  (@Bool.false)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@Eq.{(0 + 1)} (@Nat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v54) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v10 (@Fin.val (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v5) _v11) _v52))) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v54) _v3)) (@instDecidableAnd (@Eq.{(0 + 1)} (@Nat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v54) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v10 (@Fin.val (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v5) _v11) _v52))) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v54) _v3) (@instDecidableEqNat (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v54) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v10 (@Fin.val (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v5) _v11) _v52))) (@Nat.decLt (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1)
  _v54) _v3)) (@Option.none.{0} (@Bool)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v9
  _v3) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v54) (@HSub.hSub.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v9 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))
  (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) _v9 _v3) (@Eq.{(0 + 1)} (@Nat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v54) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v9 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Nat.decLt _v9 _v3)
  (@instDecidableEqNat (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v54) (@HSub.hSub.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v9 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))
  (@Option.none.{0} (@Bool)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@Eq.{(0 + 1)} (@Nat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v54) _v9) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v54) _v3)) (@instDecidableAnd (@Eq.{(0 + 1)} (@Nat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v54) _v9) (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v54) _v3) (@instDecidableEqNat (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v54) _v9) (@Nat.decLt (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v54) _v3)) (@Option.none.{0} (@Bool))
  (@PhysicalCallerClosure.callerImage _v13 _v3 _v4 _v5 _v27 _v6 _v7 _v8 _v9 (@Max.max.{0} (@Nat) (@Nat.instMax_mathlib)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0}
  (@Nat) (@instSubNat)) _v11 (@Fin.val (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))) _v5) _v11) _v52))) (@Pnp3.Core.vecOfNat _v5 (@Fin.val (@Min.min.{0} (@Nat)
  (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0}
  (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v5) _v11) _v52))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) _v8 _v7 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v54))))))))))))))))))))) (∀ (_v52 : (@Fin
  (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v5)
  _v11))),
(∀ (_v53 : (@Fin (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0,
  0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))) _v5) _v11))),
(∀ (_v54 : (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v5) _v11) _v52) (@Fin.val (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib)
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v5) _v11) _v53))),
(∀ (_v55 : (∀ (_v55 : (@Nat)),
(∀ (_v56 : (@LT.lt.{0} (@Nat) (@instLTNat) _v55 (@Fin.val (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid)))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v5) _v11) _v53))),
(@_v50 _v55)))),
(@LT.lt.{0} (@Nat) (@instLTNat) (@_v51 _v52) (@_v51 _v53))))))))) (@Or (@And (@LE.le.{0} (@Nat) (@instLENat)
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v5) _v11) (@And (∀ (_v51 : (@Nat)),
(∀ (_v52 : (@LT.lt.{0} (@Nat) (@instLTNat) _v51 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat)
  (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v5))),
(@_v50 _v51))) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v2 _v1 _v46 _v44) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1
  (@PhysicalCallerClosure.rowsDone _v0) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v26 _v43) (fun (_v51 :
  (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1))) =>
(@PhysicalCallerClosure.callerImage _v13 _v3 _v4 _v5 _v27 _v6 _v7 _v8 _v9 (@Max.max.{0} (@Nat) (@Nat.instMax_mathlib)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0}
  (@Nat) (@instSubNat)) _v11 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v5)))
  (@Pnp3.Core.vecOfNat _v5 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Pnp3.Models.Circuit.size _v5
  _v47) _v49 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v8 _v49) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v51))))))) (@Or
  (@Exists.{(0 + 1)} (@Nat) (fun (_v51 : (@Nat)) =>
(@And (@LT.lt.{0} (@Nat) (@instLTNat) _v51 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v5) _v11)) (@And (∀ (_v52 : (@Nat)),
(∀ (_v53 : (@LT.lt.{0} (@Nat) (@instLTNat) _v52 _v51)),
(@_v50 _v52))) (@And (@Not (@_v50 _v51)) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@PhysicalCallerClosure.callerMachine _v0) _v2 _v1 _v46 _v44)
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject
  (@PhysicalCallerClosure.callerMachine _v0)) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v26 _v43) (fun
  (_v52 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1))) =>
(@PhysicalCallerClosure.callerImage _v13 _v3 _v4 _v5 _v27 _v6 _v7 _v8 _v9 (@Max.max.{0} (@Nat) (@Nat.instMax_mathlib)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0}
  (@Nat) (@instSubNat)) _v11 _v51)) (@Pnp3.Core.vecOfNat _v5 _v51) (@Pnp3.Models.Circuit.size _v5 _v47) _v49
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v8 _v49) (@OfNat.ofNat.{0} (@Nat) (0 :
  Nat) (@instOfNatNat (0 : Nat))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v52)))))))))) (@And
  (@LT.lt.{0} (@Nat) (@instLTNat) _v11 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v5))
  (@And (∀ (_v51 : (@Nat)),
(∀ (_v52 : (@LT.lt.{0} (@Nat) (@instLTNat) _v51 _v11)),
(@_v50 _v51))) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v2 _v1 _v46 _v44) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@PhysicalCallerClosure.callerMachine _v0)) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v26 _v43) (fun (_v51 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v2 _v1))) =>
(@PhysicalCallerClosure.callerImage _v13 _v3 _v4 _v5 _v27 _v6 _v7 _v8 _v9 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))) (@Pnp3.Core.vecOfNat _v5 _v11) (@Pnp3.Models.Circuit.size _v5 _v47) _v49 (@HSub.hSub.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v8 _v49) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1)
  _v51)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @PhysicalCallerClosure.caller_rows_mirror

-- Independent literal expected type for PhysicalCallerClosure.copied_body.
noncomputable def PartACanonical.Types.p0558 :
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
(∀ (_v11 : (∀ (_v11 : (@Fin _v3)),
(@Bool))),
(∀ (_v12 : (∀ (_v12 : (@Fin _v5)),
(@Bool))),
(∀ (_v13 : (∀ (_v13 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v14 : (@LE.le.{0} (@Nat) (@instLENat) _v6 _v3)),
(∀ (_v15 : (@LE.le.{0} (@Nat) (@instLENat) _v3 _v2)),
(∀ (_v16 : (@LE.le.{0} (@Nat) (@instLENat) _v7 _v6)),
(∀ (_v17 : (@LE.le.{0} (@Nat) (@instLENat) _v8 _v6)),
(∀ (_v18 : (@LE.le.{0} (@Nat) (@instLENat) (@Pnp4.Frontier.ContractExpansion.bitLength _v5) _v6)),
(∀ (_v19 : (@LE.le.{0} (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v3 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) _v9 _v3)) _v6)),
(let _v20 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat))));
(let _v21 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v20 _v5) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat))));
(let _v22 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v2);
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v10)),
(∀ (_v24 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v21 _v10) _v22)),
(∀ (_v25 : (∀ (_v25 : (@Nat)),
(∀ (_v26 : (@LE.le.{0} (@Nat) (@instLENat) _v9 _v25)),
(∀ (_v27 : (@LT.lt.{0} (@Nat) (@instLTNat) _v25 _v3)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 _v25) (@Option.some.{0} (@Bool) (@_v11 (@Fin.mk _v3 _v25 _v27)))))))),
(∀ (_v26 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 _v3) (@Option.none.{0} (@Bool)))),
(∀ (_v27 : (∀ (_v27 : (@Nat)),
(∀ (_v28 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v27)),
(∀ (_v29 : (@LT.lt.{0} (@Nat) (@instLTNat) _v27 _v20)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 _v27) (@Option.some.{0} (@Bool) (@Bool.false))))))),
(∀ (_v28 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 _v20) (@Option.none.{0} (@Bool)))),
(∀ (_v29 : (∀ (_v29 : (@Fin _v5)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v21 (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Fin.val _v5 _v29))) (@Option.some.{0} (@Bool) (@_v12 _v29))))),
(∀ (_v30 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 _v21) (@Option.none.{0} (@Bool)))),
(∀ (_v31 : (∀ (_v31 : (@Nat)),
(∀ (_v32 : (@LT.lt.{0} (@Nat) (@instLTNat) _v21 _v31)),
(∀ (_v33 : (@LE.le.{0} (@Nat) (@instLENat) _v31 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v21 _v10))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 _v31) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v32 : (∀ (_v32 : (@Nat)),
(∀ (_v33 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v21 _v10) _v32)),
(∀ (_v34 : (@LT.lt.{0} (@Nat) (@instLTNat) _v32 _v22)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 _v32) (@Option.none.{0} (@Bool))))))),
(∀ (_v33 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 _v22) (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v34 : (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter _v22 _v6 _v5 (@OfNat.ofNat.{0} (@Nat) (12 : Nat)
  (@instOfNatNat (12 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1))),
(∀ (_v35 : (@LT.lt.{0} (@Nat) (@instLTNat) _v21 (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1))),
(let _v36 : (@List.{0} (@Bool)) := (@SerializedBody.window _v3 _v11 _v9 _v8);
(let _v37 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1) := (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1
  (@PhysicalCallerClosure.evalState _v0 (@SerializedBody.entry (@SerializedBody.sourceMode _v3 _v11 _v9))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v21 _v35) (fun (_v37 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v2 _v1))) =>
(@SerializedBody.prepared _v13 _v3 _v9 _v22 _v6 _v5 _v7 _v8 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1)
  _v37))));
(let _v38 : (@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool)))) := (@Bind.bind.{0, 0}
  (@Option.{0}) (@Monad.toBind.{0, 0} (@Option.{0}) (@instMonadOption.{0})) (@Prod.{0, 0} (@Pnp3.Models.Circuit _v5)
  (@List.{0} (@Bool))) (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool)))
  (@Pnp4.Frontier.ContractExpansion.decodeCircuitFull _v5 (@Pnp4.Frontier.ContractExpansion.bitLength _v5) _v36) (fun
  (_v38 : (@Prod.{0, 0} (@Pnp3.Models.Circuit _v5) (@List.{0} (@Bool)))) =>
(@PhysicalCallerClosure.copied_body.match_1.{(0 + 1)} _v5 (fun (_v39 : (@Prod.{0, 0} (@Pnp3.Models.Circuit _v5)
  (@List.{0} (@Bool)))) =>
(@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool))))) _v38 (fun (_v39 : (@Pnp3.Models.Circuit
  _v5)) =>
(fun (_v40 : (@List.{0} (@Bool))) =>
(@ite.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool)))) (@LE.le.{0} (@Nat)
  (@instLENat) (@Pnp3.Models.Circuit.size _v5 _v39) _v7) (@Nat.decLe (@Pnp3.Models.Circuit.size _v5 _v39) _v7)
  (@Option.some.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool))) (@Prod.mk.{0, 0} (@Prod.{0, 0} (@Nat)
  (@Bool)) (@List.{0} (@Bool)) (@Prod.mk.{0, 0} (@Nat) (@Bool) (@Pnp3.Models.Circuit.size _v5 _v39)
  (@Pnp3.Models.Circuit.eval _v5 _v39 _v12)) _v40)) (@Option.none.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool))
  (@List.{0} (@Bool))))))))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v39 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v39 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (1073741824 : Nat) (@instOfNatNat (1073741824 : Nat))) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))) (@And (∀ (_v40 : (@Nat)),
(∀ (_v41 : (@LE.le.{0} (@Nat) (@instLENat) _v40 _v39)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v2 _v1 _v40 _v37)) (@PhysicalCallerClosure.evalState _v0
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@SerializedBody.machine)))))) (@And (∀ (_v40 : (@Nat)),
(∀ (_v41 : (@LT.lt.{0} (@Nat) (@instLTNat) _v40 _v39)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine
  _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v2 _v1 _v40 _v37)) (@PhysicalCallerClosure.evalState _v0
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@SerializedBody.machine)))) (@And (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v2 _v1 _v40 _v37)) (@PhysicalCallerClosure.evalState _v0
  (@SerializedBody.done (@Bool.false)))) (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@PhysicalCallerClosure.callerMachine _v0) _v2 _v1 _v40 _v37))
  (@PhysicalCallerClosure.evalState _v0 (@SerializedBody.done (@Bool.true))))))))
  (@PhysicalCallerClosure.copied_body.match_3.{(0 + 1)} (fun (_v40 : (@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat)
  (@Bool)) (@List.{0} (@Bool))))) =>
(Sort 0)) _v38 (fun (_v40 : (@Unit)) =>
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v2 _v1 _v39 _v37) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1
  (@PhysicalCallerClosure.evalState _v0 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@SerializedBody.machine))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v21 _v35) (fun (_v41 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v2 _v1))) =>
(@SerializedBody.image _v13 _v22 _v6 _v5 _v7 _v8 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v3 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) _v9 _v3)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 :
  Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v41)))))) (fun (_v40 : (@Nat)) =>
(fun (_v41 : (@Bool)) =>
(fun (_v42 : (@List.{0} (@Bool))) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v43 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v43 _v8) (@And (@Eq.{(0 + 1)} (@List.{0} (@Bool)) _v42 (@List.drop.{0} (@Bool)
  _v43 _v36)) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v2 _v1 _v39 _v37) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1
  (@PhysicalCallerClosure.evalState _v0 (@SerializedBody.done _v41)) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v2
  _v1) _v21 _v35) (fun (_v44 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1))) =>
(@SerializedBody.image _v13 _v22 _v6 _v5 _v7 _v8 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v3 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) _v9 _v3)) _v40 _v43 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v8 _v43) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v44))))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @PhysicalCallerClosure.copied_body

-- Complete literal proposition for PhysicalCallerClosure.copied_body; original proof reused.
theorem PartACanonical.Surface.m0326 :
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
(∀ (_v11 : (∀ (_v11 : (@Fin _v3)),
(@Bool))),
(∀ (_v12 : (∀ (_v12 : (@Fin _v5)),
(@Bool))),
(∀ (_v13 : (∀ (_v13 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v14 : (@LE.le.{0} (@Nat) (@instLENat) _v6 _v3)),
(∀ (_v15 : (@LE.le.{0} (@Nat) (@instLENat) _v3 _v2)),
(∀ (_v16 : (@LE.le.{0} (@Nat) (@instLENat) _v7 _v6)),
(∀ (_v17 : (@LE.le.{0} (@Nat) (@instLENat) _v8 _v6)),
(∀ (_v18 : (@LE.le.{0} (@Nat) (@instLENat) (@Pnp4.Frontier.ContractExpansion.bitLength _v5) _v6)),
(∀ (_v19 : (@LE.le.{0} (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v3 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) _v9 _v3)) _v6)),
(let _v20 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat))));
(let _v21 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v20 _v5) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat))));
(let _v22 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v2);
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v10)),
(∀ (_v24 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v21 _v10) _v22)),
(∀ (_v25 : (∀ (_v25 : (@Nat)),
(∀ (_v26 : (@LE.le.{0} (@Nat) (@instLENat) _v9 _v25)),
(∀ (_v27 : (@LT.lt.{0} (@Nat) (@instLTNat) _v25 _v3)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 _v25) (@Option.some.{0} (@Bool) (@_v11 (@Fin.mk _v3 _v25 _v27)))))))),
(∀ (_v26 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 _v3) (@Option.none.{0} (@Bool)))),
(∀ (_v27 : (∀ (_v27 : (@Nat)),
(∀ (_v28 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v27)),
(∀ (_v29 : (@LT.lt.{0} (@Nat) (@instLTNat) _v27 _v20)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 _v27) (@Option.some.{0} (@Bool) (@Bool.false))))))),
(∀ (_v28 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 _v20) (@Option.none.{0} (@Bool)))),
(∀ (_v29 : (∀ (_v29 : (@Fin _v5)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v21 (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Fin.val _v5 _v29))) (@Option.some.{0} (@Bool) (@_v12 _v29))))),
(∀ (_v30 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 _v21) (@Option.none.{0} (@Bool)))),
(∀ (_v31 : (∀ (_v31 : (@Nat)),
(∀ (_v32 : (@LT.lt.{0} (@Nat) (@instLTNat) _v21 _v31)),
(∀ (_v33 : (@LE.le.{0} (@Nat) (@instLENat) _v31 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v21 _v10))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 _v31) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v32 : (∀ (_v32 : (@Nat)),
(∀ (_v33 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v21 _v10) _v32)),
(∀ (_v34 : (@LT.lt.{0} (@Nat) (@instLTNat) _v32 _v22)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 _v32) (@Option.none.{0} (@Bool))))))),
(∀ (_v33 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 _v22) (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v34 : (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter _v22 _v6 _v5 (@OfNat.ofNat.{0} (@Nat) (12 : Nat)
  (@instOfNatNat (12 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1))),
(∀ (_v35 : (@LT.lt.{0} (@Nat) (@instLTNat) _v21 (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1))),
(let _v36 : (@List.{0} (@Bool)) := (@SerializedBody.window _v3 _v11 _v9 _v8);
(let _v37 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1) := (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1
  (@PhysicalCallerClosure.evalState _v0 (@SerializedBody.entry (@SerializedBody.sourceMode _v3 _v11 _v9))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v21 _v35) (fun (_v37 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v2 _v1))) =>
(@SerializedBody.prepared _v13 _v3 _v9 _v22 _v6 _v5 _v7 _v8 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1)
  _v37))));
(let _v38 : (@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool)))) := (@Bind.bind.{0, 0}
  (@Option.{0}) (@Monad.toBind.{0, 0} (@Option.{0}) (@instMonadOption.{0})) (@Prod.{0, 0} (@Pnp3.Models.Circuit _v5)
  (@List.{0} (@Bool))) (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool)))
  (@Pnp4.Frontier.ContractExpansion.decodeCircuitFull _v5 (@Pnp4.Frontier.ContractExpansion.bitLength _v5) _v36) (fun
  (_v38 : (@Prod.{0, 0} (@Pnp3.Models.Circuit _v5) (@List.{0} (@Bool)))) =>
(@PhysicalCallerClosure.copied_body.match_1.{(0 + 1)} _v5 (fun (_v39 : (@Prod.{0, 0} (@Pnp3.Models.Circuit _v5)
  (@List.{0} (@Bool)))) =>
(@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool))))) _v38 (fun (_v39 : (@Pnp3.Models.Circuit
  _v5)) =>
(fun (_v40 : (@List.{0} (@Bool))) =>
(@ite.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool)))) (@LE.le.{0} (@Nat)
  (@instLENat) (@Pnp3.Models.Circuit.size _v5 _v39) _v7) (@Nat.decLe (@Pnp3.Models.Circuit.size _v5 _v39) _v7)
  (@Option.some.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool))) (@Prod.mk.{0, 0} (@Prod.{0, 0} (@Nat)
  (@Bool)) (@List.{0} (@Bool)) (@Prod.mk.{0, 0} (@Nat) (@Bool) (@Pnp3.Models.Circuit.size _v5 _v39)
  (@Pnp3.Models.Circuit.eval _v5 _v39 _v12)) _v40)) (@Option.none.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool))
  (@List.{0} (@Bool))))))))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v39 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v39 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (1073741824 : Nat) (@instOfNatNat (1073741824 : Nat))) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))) (@And (∀ (_v40 : (@Nat)),
(∀ (_v41 : (@LE.le.{0} (@Nat) (@instLENat) _v40 _v39)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v2 _v1 _v40 _v37)) (@PhysicalCallerClosure.evalState _v0
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@SerializedBody.machine)))))) (@And (∀ (_v40 : (@Nat)),
(∀ (_v41 : (@LT.lt.{0} (@Nat) (@instLTNat) _v40 _v39)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine
  _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v2 _v1 _v40 _v37)) (@PhysicalCallerClosure.evalState _v0
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@SerializedBody.machine)))) (@And (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v2 _v1 _v40 _v37)) (@PhysicalCallerClosure.evalState _v0
  (@SerializedBody.done (@Bool.false)))) (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@PhysicalCallerClosure.callerMachine _v0) _v2 _v1 _v40 _v37))
  (@PhysicalCallerClosure.evalState _v0 (@SerializedBody.done (@Bool.true))))))))
  (@PhysicalCallerClosure.copied_body.match_3.{(0 + 1)} (fun (_v40 : (@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat)
  (@Bool)) (@List.{0} (@Bool))))) =>
(Sort 0)) _v38 (fun (_v40 : (@Unit)) =>
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v2 _v1 _v39 _v37) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1
  (@PhysicalCallerClosure.evalState _v0 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@SerializedBody.machine))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v21 _v35) (fun (_v41 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v2 _v1))) =>
(@SerializedBody.image _v13 _v22 _v6 _v5 _v7 _v8 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v3 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) _v9 _v3)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 :
  Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v41)))))) (fun (_v40 : (@Nat)) =>
(fun (_v41 : (@Bool)) =>
(fun (_v42 : (@List.{0} (@Bool))) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v43 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v43 _v8) (@And (@Eq.{(0 + 1)} (@List.{0} (@Bool)) _v42 (@List.drop.{0} (@Bool)
  _v43 _v36)) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v2 _v1 _v39 _v37) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1
  (@PhysicalCallerClosure.evalState _v0 (@SerializedBody.done _v41)) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v2
  _v1) _v21 _v35) (fun (_v44 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1))) =>
(@SerializedBody.image _v13 _v22 _v6 _v5 _v7 _v8 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v3 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) _v9 _v3)) _v40 _v43 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v8 _v43) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v44))))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @PhysicalCallerClosure.copied_body

-- Independent literal expected type for PhysicalCallerClosure.copied_body_mirror.
noncomputable def PartACanonical.Types.p0559 :
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
(∀ (_v11 : (∀ (_v11 : (@Fin _v3)),
(@Bool))),
(∀ (_v12 : (∀ (_v12 : (@Fin _v5)),
(@Bool))),
(∀ (_v13 : (∀ (_v13 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v14 : (@LE.le.{0} (@Nat) (@instLENat) _v6 _v3)),
(∀ (_v15 : (@LE.le.{0} (@Nat) (@instLENat) _v3 _v2)),
(∀ (_v16 : (@LE.le.{0} (@Nat) (@instLENat) _v7 _v6)),
(∀ (_v17 : (@LE.le.{0} (@Nat) (@instLENat) _v8 _v6)),
(∀ (_v18 : (@LE.le.{0} (@Nat) (@instLENat) (@Pnp4.Frontier.ContractExpansion.bitLength _v5) _v6)),
(∀ (_v19 : (@LE.le.{0} (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v3 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) _v9 _v3)) _v6)),
(let _v20 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat))));
(let _v21 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v20 _v5) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat))));
(let _v22 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v2);
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v10)),
(∀ (_v24 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v21 _v10) _v22)),
(∀ (_v25 : (∀ (_v25 : (@Nat)),
(∀ (_v26 : (@LE.le.{0} (@Nat) (@instLENat) _v9 _v25)),
(∀ (_v27 : (@LT.lt.{0} (@Nat) (@instLTNat) _v25 _v3)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 _v25) (@Option.some.{0} (@Bool) (@_v11 (@Fin.mk _v3 _v25 _v27)))))))),
(∀ (_v26 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 _v3) (@Option.none.{0} (@Bool)))),
(∀ (_v27 : (∀ (_v27 : (@Nat)),
(∀ (_v28 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v27)),
(∀ (_v29 : (@LT.lt.{0} (@Nat) (@instLTNat) _v27 _v20)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 _v27) (@Option.some.{0} (@Bool) (@Bool.false))))))),
(∀ (_v28 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 _v20) (@Option.none.{0} (@Bool)))),
(∀ (_v29 : (∀ (_v29 : (@Fin _v5)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v21 (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Fin.val _v5 _v29))) (@Option.some.{0} (@Bool) (@_v12 _v29))))),
(∀ (_v30 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 _v21) (@Option.none.{0} (@Bool)))),
(∀ (_v31 : (∀ (_v31 : (@Nat)),
(∀ (_v32 : (@LT.lt.{0} (@Nat) (@instLTNat) _v21 _v31)),
(∀ (_v33 : (@LE.le.{0} (@Nat) (@instLENat) _v31 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v21 _v10))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 _v31) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v32 : (∀ (_v32 : (@Nat)),
(∀ (_v33 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v21 _v10) _v32)),
(∀ (_v34 : (@LT.lt.{0} (@Nat) (@instLTNat) _v32 _v22)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 _v32) (@Option.none.{0} (@Bool))))))),
(∀ (_v33 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 _v22) (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v34 : (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter _v22 _v6 _v5 (@OfNat.ofNat.{0} (@Nat) (12 : Nat)
  (@instOfNatNat (12 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1))),
(∀ (_v35 : (@LT.lt.{0} (@Nat) (@instLTNat) _v21 (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1))),
(let _v36 : (@List.{0} (@Bool)) := (@SerializedBody.window _v3 _v11 _v9 _v8);
(let _v37 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1) := (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1
  (@PhysicalCallerClosure.evalState _v0 (@SerializedBody.entry (@SerializedBody.sourceMode _v3 _v11 _v9))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v21 _v35) (fun (_v37 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v2 _v1))) =>
(@SerializedBody.prepared _v13 _v3 _v9 _v22 _v6 _v5 _v7 _v8 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1)
  _v37))));
(let _v38 : (@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool)))) := (@Bind.bind.{0, 0}
  (@Option.{0}) (@Monad.toBind.{0, 0} (@Option.{0}) (@instMonadOption.{0})) (@Prod.{0, 0} (@Pnp3.Models.Circuit _v5)
  (@List.{0} (@Bool))) (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool)))
  (@Pnp4.Frontier.ContractExpansion.decodeCircuitFull _v5 (@Pnp4.Frontier.ContractExpansion.bitLength _v5) _v36) (fun
  (_v38 : (@Prod.{0, 0} (@Pnp3.Models.Circuit _v5) (@List.{0} (@Bool)))) =>
(@PhysicalCallerClosure.copied_body_mirror.match_1.{(0 + 1)} _v5 (fun (_v39 : (@Prod.{0, 0} (@Pnp3.Models.Circuit _v5)
  (@List.{0} (@Bool)))) =>
(@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool))))) _v38 (fun (_v39 : (@Pnp3.Models.Circuit
  _v5)) =>
(fun (_v40 : (@List.{0} (@Bool))) =>
(@ite.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool)))) (@LE.le.{0} (@Nat)
  (@instLENat) (@Pnp3.Models.Circuit.size _v5 _v39) _v7) (@Nat.decLe (@Pnp3.Models.Circuit.size _v5 _v39) _v7)
  (@Option.some.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool))) (@Prod.mk.{0, 0} (@Prod.{0, 0} (@Nat)
  (@Bool)) (@List.{0} (@Bool)) (@Prod.mk.{0, 0} (@Nat) (@Bool) (@Pnp3.Models.Circuit.size _v5 _v39)
  (@Pnp3.Models.Circuit.eval _v5 _v39 _v12)) _v40)) (@Option.none.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool))
  (@List.{0} (@Bool))))))))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v39 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v39 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (1073741824 : Nat) (@instOfNatNat (1073741824 : Nat))) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))) (@And (∀ (_v40 : (@Nat)),
(∀ (_v41 : (@LE.le.{0} (@Nat) (@instLENat) _v40 _v39)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v2 _v1 _v40 _v37)) (@PhysicalCallerClosure.evalState _v0
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@SerializedBody.machine)))))) (@And (∀ (_v40 : (@Nat)),
(∀ (_v41 : (@LT.lt.{0} (@Nat) (@instLTNat) _v40 _v39)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine
  _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v2 _v1 _v40 _v37)) (@PhysicalCallerClosure.evalState _v0
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@SerializedBody.machine)))) (@And (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v2 _v1 _v40 _v37)) (@PhysicalCallerClosure.evalState _v0
  (@SerializedBody.done (@Bool.false)))) (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@PhysicalCallerClosure.callerMachine _v0) _v2 _v1 _v40 _v37))
  (@PhysicalCallerClosure.evalState _v0 (@SerializedBody.done (@Bool.true))))))))
  (@PhysicalCallerClosure.copied_body_mirror.match_3.{(0 + 1)} (fun (_v40 : (@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0}
  (@Nat) (@Bool)) (@List.{0} (@Bool))))) =>
(Sort 0)) _v38 (fun (_v40 : (@Unit)) =>
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v2 _v1 _v39 _v37) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1
  (@PhysicalCallerClosure.evalState _v0 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@SerializedBody.machine))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v21 _v35) (fun (_v41 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v2 _v1))) =>
(@SerializedBody.image _v13 _v22 _v6 _v5 _v7 _v8 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v3 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) _v9 _v3)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 :
  Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v41)))))) (fun (_v40 : (@Nat)) =>
(fun (_v41 : (@Bool)) =>
(fun (_v42 : (@List.{0} (@Bool))) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v43 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v43 _v8) (@And (@Eq.{(0 + 1)} (@List.{0} (@Bool)) _v42 (@List.drop.{0} (@Bool)
  _v43 _v36)) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v2 _v1 _v39 _v37) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1
  (@PhysicalCallerClosure.evalState _v0 (@SerializedBody.done _v41)) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v2
  _v1) _v21 _v35) (fun (_v44 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1))) =>
(@SerializedBody.image _v13 _v22 _v6 _v5 _v7 _v8 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v3 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) _v9 _v3)) _v40 _v43 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v8 _v43) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v44))))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @PhysicalCallerClosure.copied_body_mirror

-- Complete literal proposition for PhysicalCallerClosure.copied_body_mirror; original proof reused.
theorem PartACanonical.Surface.m0327 :
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
(∀ (_v11 : (∀ (_v11 : (@Fin _v3)),
(@Bool))),
(∀ (_v12 : (∀ (_v12 : (@Fin _v5)),
(@Bool))),
(∀ (_v13 : (∀ (_v13 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v14 : (@LE.le.{0} (@Nat) (@instLENat) _v6 _v3)),
(∀ (_v15 : (@LE.le.{0} (@Nat) (@instLENat) _v3 _v2)),
(∀ (_v16 : (@LE.le.{0} (@Nat) (@instLENat) _v7 _v6)),
(∀ (_v17 : (@LE.le.{0} (@Nat) (@instLENat) _v8 _v6)),
(∀ (_v18 : (@LE.le.{0} (@Nat) (@instLENat) (@Pnp4.Frontier.ContractExpansion.bitLength _v5) _v6)),
(∀ (_v19 : (@LE.le.{0} (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v3 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) _v9 _v3)) _v6)),
(let _v20 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat))));
(let _v21 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v20 _v5) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat))));
(let _v22 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v2);
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v10)),
(∀ (_v24 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v21 _v10) _v22)),
(∀ (_v25 : (∀ (_v25 : (@Nat)),
(∀ (_v26 : (@LE.le.{0} (@Nat) (@instLENat) _v9 _v25)),
(∀ (_v27 : (@LT.lt.{0} (@Nat) (@instLTNat) _v25 _v3)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 _v25) (@Option.some.{0} (@Bool) (@_v11 (@Fin.mk _v3 _v25 _v27)))))))),
(∀ (_v26 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 _v3) (@Option.none.{0} (@Bool)))),
(∀ (_v27 : (∀ (_v27 : (@Nat)),
(∀ (_v28 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v27)),
(∀ (_v29 : (@LT.lt.{0} (@Nat) (@instLTNat) _v27 _v20)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 _v27) (@Option.some.{0} (@Bool) (@Bool.false))))))),
(∀ (_v28 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 _v20) (@Option.none.{0} (@Bool)))),
(∀ (_v29 : (∀ (_v29 : (@Fin _v5)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v21 (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Fin.val _v5 _v29))) (@Option.some.{0} (@Bool) (@_v12 _v29))))),
(∀ (_v30 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 _v21) (@Option.none.{0} (@Bool)))),
(∀ (_v31 : (∀ (_v31 : (@Nat)),
(∀ (_v32 : (@LT.lt.{0} (@Nat) (@instLTNat) _v21 _v31)),
(∀ (_v33 : (@LE.le.{0} (@Nat) (@instLENat) _v31 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v21 _v10))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 _v31) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v32 : (∀ (_v32 : (@Nat)),
(∀ (_v33 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v21 _v10) _v32)),
(∀ (_v34 : (@LT.lt.{0} (@Nat) (@instLTNat) _v32 _v22)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 _v32) (@Option.none.{0} (@Bool))))))),
(∀ (_v33 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v13 _v22) (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v34 : (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter _v22 _v6 _v5 (@OfNat.ofNat.{0} (@Nat) (12 : Nat)
  (@instOfNatNat (12 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1))),
(∀ (_v35 : (@LT.lt.{0} (@Nat) (@instLTNat) _v21 (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1))),
(let _v36 : (@List.{0} (@Bool)) := (@SerializedBody.window _v3 _v11 _v9 _v8);
(let _v37 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1) := (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1
  (@PhysicalCallerClosure.evalState _v0 (@SerializedBody.entry (@SerializedBody.sourceMode _v3 _v11 _v9))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v21 _v35) (fun (_v37 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v2 _v1))) =>
(@SerializedBody.prepared _v13 _v3 _v9 _v22 _v6 _v5 _v7 _v8 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1)
  _v37))));
(let _v38 : (@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool)))) := (@Bind.bind.{0, 0}
  (@Option.{0}) (@Monad.toBind.{0, 0} (@Option.{0}) (@instMonadOption.{0})) (@Prod.{0, 0} (@Pnp3.Models.Circuit _v5)
  (@List.{0} (@Bool))) (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool)))
  (@Pnp4.Frontier.ContractExpansion.decodeCircuitFull _v5 (@Pnp4.Frontier.ContractExpansion.bitLength _v5) _v36) (fun
  (_v38 : (@Prod.{0, 0} (@Pnp3.Models.Circuit _v5) (@List.{0} (@Bool)))) =>
(@PhysicalCallerClosure.copied_body_mirror.match_1.{(0 + 1)} _v5 (fun (_v39 : (@Prod.{0, 0} (@Pnp3.Models.Circuit _v5)
  (@List.{0} (@Bool)))) =>
(@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool))))) _v38 (fun (_v39 : (@Pnp3.Models.Circuit
  _v5)) =>
(fun (_v40 : (@List.{0} (@Bool))) =>
(@ite.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool)))) (@LE.le.{0} (@Nat)
  (@instLENat) (@Pnp3.Models.Circuit.size _v5 _v39) _v7) (@Nat.decLe (@Pnp3.Models.Circuit.size _v5 _v39) _v7)
  (@Option.some.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool))) (@Prod.mk.{0, 0} (@Prod.{0, 0} (@Nat)
  (@Bool)) (@List.{0} (@Bool)) (@Prod.mk.{0, 0} (@Nat) (@Bool) (@Pnp3.Models.Circuit.size _v5 _v39)
  (@Pnp3.Models.Circuit.eval _v5 _v39 _v12)) _v40)) (@Option.none.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool))
  (@List.{0} (@Bool))))))))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v39 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v39 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (1073741824 : Nat) (@instOfNatNat (1073741824 : Nat))) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))) (@And (∀ (_v40 : (@Nat)),
(∀ (_v41 : (@LE.le.{0} (@Nat) (@instLENat) _v40 _v39)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v2 _v1 _v40 _v37)) (@PhysicalCallerClosure.evalState _v0
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@SerializedBody.machine)))))) (@And (∀ (_v40 : (@Nat)),
(∀ (_v41 : (@LT.lt.{0} (@Nat) (@instLTNat) _v40 _v39)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine
  _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v2 _v1 _v40 _v37)) (@PhysicalCallerClosure.evalState _v0
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@SerializedBody.machine)))) (@And (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v2 _v1 _v40 _v37)) (@PhysicalCallerClosure.evalState _v0
  (@SerializedBody.done (@Bool.false)))) (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@PhysicalCallerClosure.callerMachine _v0) _v2 _v1 _v40 _v37))
  (@PhysicalCallerClosure.evalState _v0 (@SerializedBody.done (@Bool.true))))))))
  (@PhysicalCallerClosure.copied_body_mirror.match_3.{(0 + 1)} (fun (_v40 : (@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0}
  (@Nat) (@Bool)) (@List.{0} (@Bool))))) =>
(Sort 0)) _v38 (fun (_v40 : (@Unit)) =>
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v2 _v1 _v39 _v37) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1
  (@PhysicalCallerClosure.evalState _v0 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@SerializedBody.machine))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v21 _v35) (fun (_v41 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v2 _v1))) =>
(@SerializedBody.image _v13 _v22 _v6 _v5 _v7 _v8 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v3 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) _v9 _v3)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 :
  Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v41)))))) (fun (_v40 : (@Nat)) =>
(fun (_v41 : (@Bool)) =>
(fun (_v42 : (@List.{0} (@Bool))) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v43 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v43 _v8) (@And (@Eq.{(0 + 1)} (@List.{0} (@Bool)) _v42 (@List.drop.{0} (@Bool)
  _v43 _v36)) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v2 _v1 _v39 _v37) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v2 _v1
  (@PhysicalCallerClosure.evalState _v0 (@SerializedBody.done _v41)) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v2
  _v1) _v21 _v35) (fun (_v44 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1))) =>
(@SerializedBody.image _v13 _v22 _v6 _v5 _v7 _v8 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v3 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) _v9 _v3)) _v40 _v43 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v8 _v43) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v2 _v1) _v44))))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @PhysicalCallerClosure.copied_body_mirror

-- Independent literal expected type for PhysicalCallerClosure.evalState.
noncomputable def PartACanonical.Types.p0560 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)))),
(@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0))))) := by
  exact @PhysicalCallerClosure.evalState

-- Independent literal expected type for PhysicalCallerClosure.eval_prefix.
noncomputable def PartACanonical.Types.p0561 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ {_v3 : (@Nat)},
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v1 _v2)),
(∀ (_v5 : (∀ (_v5 : (@Nat)),
(∀ (_v6 : (@LT.lt.{0} (@Nat) (@instLTNat) _v5 _v3)),
(@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v1 _v2 _v5 _v4))))))),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@LE.le.{0} (@Nat) (@instLENat) _v6 _v3)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v1 _v2 _v6 (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v1 _v2
  (@PhysicalCallerClosure.evalState _v0 (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v1 _v2 _v4))
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))
  _v1 _v2 _v4) (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v1 _v2 _v4))) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v1 _v2
  (@PhysicalCallerClosure.evalState _v0 (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v1 _v2 _v6 _v4)))
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))
  _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v1 _v2 _v6 _v4))
  (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))
  _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v1 _v2 _v6 _v4)))))))))))) := by
  exact @PhysicalCallerClosure.eval_prefix

-- Complete literal proposition for PhysicalCallerClosure.eval_prefix; original proof reused.
theorem PartACanonical.Surface.m0328 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ {_v3 : (@Nat)},
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v1 _v2)),
(∀ (_v5 : (∀ (_v5 : (@Nat)),
(∀ (_v6 : (@LT.lt.{0} (@Nat) (@instLTNat) _v5 _v3)),
(@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v1 _v2 _v5 _v4))))))),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@LE.le.{0} (@Nat) (@instLENat) _v6 _v3)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v1 _v2 _v6 (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v1 _v2
  (@PhysicalCallerClosure.evalState _v0 (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v1 _v2 _v4))
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))
  _v1 _v2 _v4) (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v1 _v2 _v4))) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v1 _v2
  (@PhysicalCallerClosure.evalState _v0 (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v1 _v2 _v6 _v4)))
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))
  _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v1 _v2 _v6 _v4))
  (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))
  _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v1 _v2 _v6 _v4)))))))))))) := by
  exact @PhysicalCallerClosure.eval_prefix

-- Independent literal expected type for PhysicalCallerClosure.eval_prefix_mirror.
noncomputable def PartACanonical.Types.p0562 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ {_v3 : (@Nat)},
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v1 _v2)),
(∀ (_v5 : (∀ (_v5 : (@Nat)),
(∀ (_v6 : (@LT.lt.{0} (@Nat) (@instLTNat) _v5 _v3)),
(@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v1 _v2 _v5 _v4))))))),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@LE.le.{0} (@Nat) (@instLENat) _v6 _v3)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v1 _v2 _v6 (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v1 _v2
  (@PhysicalCallerClosure.evalState _v0 (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v1 _v2 _v4))
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))
  _v1 _v2 _v4) (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v1 _v2 _v4))) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v1 _v2
  (@PhysicalCallerClosure.evalState _v0 (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v1 _v2 _v6 _v4)))
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))
  _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v1 _v2 _v6 _v4))
  (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))
  _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v1 _v2 _v6 _v4)))))))))))) := by
  exact @PhysicalCallerClosure.eval_prefix_mirror

-- Complete literal proposition for PhysicalCallerClosure.eval_prefix_mirror; original proof reused.
theorem PartACanonical.Surface.m0329 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ {_v3 : (@Nat)},
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v1 _v2)),
(∀ (_v5 : (∀ (_v5 : (@Nat)),
(∀ (_v6 : (@LT.lt.{0} (@Nat) (@instLTNat) _v5 _v3)),
(@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v1 _v2 _v5 _v4))))))),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@LE.le.{0} (@Nat) (@instLENat) _v6 _v3)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0)) _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PhysicalCallerClosure.callerMachine _v0) _v1 _v2 _v6 (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v1 _v2
  (@PhysicalCallerClosure.evalState _v0 (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v1 _v2 _v4))
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))
  _v1 _v2 _v4) (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v1 _v2 _v4))) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0)) _v1 _v2
  (@PhysicalCallerClosure.evalState _v0 (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v1 _v2 _v6 _v4)))
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))
  _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v1 _v2 _v6 _v4))
  (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))
  _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v1 _v2 _v6 _v4)))))))))))) := by
  exact @PhysicalCallerClosure.eval_prefix_mirror

-- Independent literal expected type for PhysicalCallerClosure.eval_rows.
noncomputable def PartACanonical.Types.p0563 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)))),
(∀ (_v2 : (@Option.{0} (@Bool))),
(∀ (_v3 : (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v1))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@PhysicalCallerClosure.callerMachine _v0) (@PhysicalCallerClosure.evalState
  _v0 _v1) _v2) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))
  (@PhysicalCallerClosure.evalState _v0 (@Prod.fst.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@SerializedBody.machine) _v1 _v2))) (@Prod.snd.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@SerializedBody.machine) _v1
  _v2)))))))) := by
  exact @PhysicalCallerClosure.eval_rows

-- Complete literal proposition for PhysicalCallerClosure.eval_rows; original proof reused.
theorem PartACanonical.Surface.m0330 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)))),
(∀ (_v2 : (@Option.{0} (@Bool))),
(∀ (_v3 : (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v1))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@PhysicalCallerClosure.callerMachine _v0) (@PhysicalCallerClosure.evalState
  _v0 _v1) _v2) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))
  (@PhysicalCallerClosure.evalState _v0 (@Prod.fst.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@SerializedBody.machine) _v1 _v2))) (@Prod.snd.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@SerializedBody.machine) _v1
  _v2)))))))) := by
  exact @PhysicalCallerClosure.eval_rows

-- Independent literal expected type for PhysicalCallerClosure.eval_rows_mirror.
noncomputable def PartACanonical.Types.p0564 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)))),
(∀ (_v2 : (@Option.{0} (@Bool))),
(∀ (_v3 : (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v1))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@PhysicalCallerClosure.callerMachine _v0) (@PhysicalCallerClosure.evalState
  _v0 _v1) _v2) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))
  (@PhysicalCallerClosure.evalState _v0 (@Prod.fst.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@SerializedBody.machine) _v1 _v2))) (@Prod.snd.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@SerializedBody.machine) _v1
  _v2)))))))) := by
  exact @PhysicalCallerClosure.eval_rows_mirror

-- Complete literal proposition for PhysicalCallerClosure.eval_rows_mirror; original proof reused.
theorem PartACanonical.Surface.m0331 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)))),
(∀ (_v2 : (@Option.{0} (@Bool))),
(∀ (_v3 : (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v1))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@PhysicalCallerClosure.callerMachine _v0) (@PhysicalCallerClosure.evalState
  _v0 _v1) _v2) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))
  (@PhysicalCallerClosure.evalState _v0 (@Prod.fst.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@SerializedBody.machine) _v1 _v2))) (@Prod.snd.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@SerializedBody.machine) _v1
  _v2)))))))) := by
  exact @PhysicalCallerClosure.eval_rows_mirror

-- Independent literal expected type for PhysicalCallerClosure.installed_body.
noncomputable def PartACanonical.Types.p0565 :
(∀ (_v0 : (@Nat)),
(@PhysicalCallerClosure.InstalledBody _v0)) := by
  exact @PhysicalCallerClosure.installed_body

-- Complete literal proposition for PhysicalCallerClosure.installed_body; original proof reused.
theorem PartACanonical.Surface.m0332 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Nat)),
(∀ (_v8 : (@Nat)),
(∀ (_v9 : (∀ (_v9 : (@Fin _v2)),
(@Bool))),
(∀ (_v10 : (∀ (_v10 : (@Fin _v4)),
(@Bool))),
(∀ (_v11 : (∀ (_v11 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v12 : (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) _v1)),
(∀ (_v13 : (@LE.le.{0} (@Nat) (@instLENat) _v2 _v1)),
(∀ (_v14 : (@LE.le.{0} (@Nat) (@instLENat) _v4 _v1)),
(∀ (_v15 : (@LT.lt.{0} (@Nat) (@instLTNat) _v5 _v2)),
(let _v16 : (@Nat) := (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v2 _v5);
(let _v17 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v3) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat))));
(let _v18 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v17 _v4) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat))));
(let _v19 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v1);
(let _v20 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation _v1);
(let _v21 : (∀ (_v21 : (@Nat)),
(@Nat)) := (@SerializedBody.delimiter _v19 _v16 _v4);
(∀ (_v22 : (@LE.le.{0} (@Nat) (@instLENat) _v6 _v16)),
(∀ (_v23 : (@LE.le.{0} (@Nat) (@instLENat) _v7 _v16)),
(∀ (_v24 : (@LE.le.{0} (@Nat) (@instLENat) (@Pnp4.Frontier.ContractExpansion.bitLength _v4) _v16)),
(∀ (_v25 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v8)),
(∀ (_v26 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v18 _v8) _v19)),
(∀ (_v27 : (∀ (_v27 : (@Nat)),
(∀ (_v28 : (@LE.le.{0} (@Nat) (@instLENat) _v5 _v27)),
(∀ (_v29 : (@LT.lt.{0} (@Nat) (@instLTNat) _v27 _v2)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v11 _v27) (@Option.some.{0} (@Bool) (@_v9 (@Fin.mk _v2 _v27 _v29)))))))),
(∀ (_v28 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v11 _v2) (@Option.none.{0} (@Bool)))),
(∀ (_v29 : (∀ (_v29 : (@Nat)),
(∀ (_v30 : (@LT.lt.{0} (@Nat) (@instLTNat) _v2 _v29)),
(∀ (_v31 : (@LT.lt.{0} (@Nat) (@instLTNat) _v29 _v17)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v11 _v29) (@Option.some.{0} (@Bool) (@Bool.false))))))),
(∀ (_v30 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v11 _v17) (@Option.none.{0} (@Bool)))),
(∀ (_v31 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v11 _v18) (@Option.none.{0} (@Bool)))),
(∀ (_v32 : (∀ (_v32 : (@Fin _v4)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v11 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v18 (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Fin.val _v4 _v32))) (@Option.some.{0} (@Bool) (@_v10 _v32))))),
(∀ (_v33 : (∀ (_v33 : (@Nat)),
(∀ (_v34 : (@LT.lt.{0} (@Nat) (@instLTNat) _v18 _v33)),
(∀ (_v35 : (@LE.le.{0} (@Nat) (@instLENat) _v33 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v18 _v8))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v11 _v33) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v34 : (∀ (_v34 : (@Nat)),
(∀ (_v35 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v18 _v8) _v34)),
(∀ (_v36 : (@LT.lt.{0} (@Nat) (@instLTNat) _v34 _v19)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v11 _v34) (@Option.none.{0} (@Bool))))))),
(∀ (_v35 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v11 _v19) (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v36 : (∀ (_v36 : (@Nat)),
(∀ (_v37 : (@LE.le.{0} (@Nat) (@instLENat) _v36 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v11 (@_v21 _v36)) (@Option.none.{0} (@Bool)))))),
(∀ (_v37 : (∀ (_v37 : (@Nat)),
(∀ (_v38 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v21 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v37)),
(∀ (_v39 : (@LT.lt.{0} (@Nat) (@instLTNat) _v37 (@_v21 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v11 _v37) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat)
  (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v37 (@_v21
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))) _v6) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v37 (@_v21 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))))
  _v6)))))))),
(∀ (_v38 : (∀ (_v38 : (@Nat)),
(∀ (_v39 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v21 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v38)),
(∀ (_v40 : (@LT.lt.{0} (@Nat) (@instLTNat) _v38 (@_v21 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v11 _v38) (@Option.some.{0} (@Bool) (@Bool.false))))))),
(∀ (_v39 : (∀ (_v39 : (@Nat)),
(∀ (_v40 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v21 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v39)),
(∀ (_v41 : (@LT.lt.{0} (@Nat) (@instLTNat) _v39 (@_v21 (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v11 _v39) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat)
  (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v39 (@_v21
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))) (@Pnp4.Frontier.ContractExpansion.bitLength _v7))
  (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v39 (@_v21
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))) (@Pnp4.Frontier.ContractExpansion.bitLength
  _v7))))))))),
(∀ (_v40 : (∀ (_v40 : (@Nat)),
(∀ (_v41 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v21 (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v40)),
(∀ (_v42 : (@LT.lt.{0} (@Nat) (@instLTNat) _v40 (@_v21 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))),
(∀ (_v43 : (@Ne.{(0 + 1)} (@Nat) _v40 (@_v21 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v11 _v40) (@Option.some.{0} (@Bool) (@Bool.false)))))))),
(∀ (_v41 : (∀ (_v41 : (@Nat)),
(∀ (_v42 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v21 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) _v41)),
(∀ (_v43 : (@LT.lt.{0} (@Nat) (@instLTNat) _v41 (@_v21 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v11 _v41) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat)
  (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v41 (@_v21
  (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))) _v7) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v41 (@_v21 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))
  _v7)))))))),
(∀ (_v42 : (∀ (_v42 : (@Nat)),
(∀ (_v43 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v21 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) _v42)),
(∀ (_v44 : (@LE.le.{0} (@Nat) (@instLENat) _v42 (@_v21 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 :
  Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v11 _v42) (@Option.none.{0} (@Bool))))))),
(∀ (_v43 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v21 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v20))),
(∀ (_v44 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v21 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v20))),
(∀ (_v45 : (@LT.lt.{0} (@Nat) (@instLTNat) _v18 (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v20))),
(let _v46 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine
  _v0)) _v1 _v20) := (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@BodyIngress.machine _v0)) _v1 _v20 (@BodyIngress.old _v0 (@CarryWindow.ready _v0)) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v20) (@_v21 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  _v44) (fun (_v46 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v20))) =>
(@_v11 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v20) _v46))));
(let _v47 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v5 (@Pnp4.Frontier.ContractExpansion.bitLength _v7)) _v7);
(let _v48 : (@List.{0} (@Bool)) := (@SerializedBody.window _v2 _v9 _v47 _v7);
(let _v49 : (@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool)))) := (@Bind.bind.{0, 0}
  (@Option.{0}) (@Monad.toBind.{0, 0} (@Option.{0}) (@instMonadOption.{0})) (@Prod.{0, 0} (@Pnp3.Models.Circuit _v4)
  (@List.{0} (@Bool))) (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool)))
  (@Pnp4.Frontier.ContractExpansion.decodeCircuitFull _v4 (@Pnp4.Frontier.ContractExpansion.bitLength _v4) _v48) (fun
  (_v49 : (@Prod.{0, 0} (@Pnp3.Models.Circuit _v4) (@List.{0} (@Bool)))) =>
(@PhysicalCallerClosure.InstalledBody.match_1.{(0 + 1)} _v4 (fun (_v50 : (@Prod.{0, 0} (@Pnp3.Models.Circuit _v4)
  (@List.{0} (@Bool)))) =>
(@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool))))) _v49 (fun (_v50 : (@Pnp3.Models.Circuit
  _v4)) =>
(fun (_v51 : (@List.{0} (@Bool))) =>
(@ite.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool)))) (@LE.le.{0} (@Nat)
  (@instLENat) (@Pnp3.Models.Circuit.size _v4 _v50) _v6) (@Nat.decLe (@Pnp3.Models.Circuit.size _v4 _v50) _v6)
  (@Option.some.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool))) (@Prod.mk.{0, 0} (@Prod.{0, 0} (@Nat)
  (@Bool)) (@List.{0} (@Bool)) (@Prod.mk.{0, 0} (@Nat) (@Bool) (@Pnp3.Models.Circuit.size _v4 _v50)
  (@Pnp3.Models.Circuit.eval _v4 _v50 _v10)) _v51)) (@Option.none.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool))
  (@List.{0} (@Bool))))))))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v50 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v51 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v50 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (1073741824 : Nat) (@instOfNatNat (1073741824 : Nat))) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))))) (@And (@LE.le.{0} (@Nat) (@instLENat) _v51
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (1073741824 :
  Nat) (@instOfNatNat (1073741824 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (6 : Nat)
  (@instOfNatNat (6 : Nat)))))) (@And (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v50 _v51) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2147483648 : Nat) (@instOfNatNat (2147483648 : Nat))) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))) (@And (∀ (_v52 : (@Nat)),
(∀ (_v53 : (@LE.le.{0} (@Nat) (@instLENat) _v52 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v50 _v51))),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  _v1 _v20 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@BodyIngress.machine _v0) _v1 _v20 _v52 _v46))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@BodyIngress.machine _v0))))) (@And (∀ (_v52 : (@Nat)),
(∀ (_v53 : (@LT.lt.{0} (@Nat) (@instLTNat) _v52 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v50 _v51))),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  _v1 _v20 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@BodyIngress.machine _v0) _v1 _v20 _v52 _v46))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@BodyIngress.machine _v0))) (@And (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)) _v1 _v20
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@BodyIngress.machine _v0) _v1 _v20 _v52 _v46)) (@BodyIngress.body _v0
  (@SerializedBody.done (@Bool.false)))) (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@BodyIngress.machine _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@BodyIngress.machine _v0)) _v1 _v20 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@BodyIngress.machine _v0) _v1 _v20 _v52
  _v46)) (@BodyIngress.body _v0 (@SerializedBody.done (@Bool.true))))))))
  (@PhysicalCallerClosure.InstalledBody.match_3.{(0 + 1)} (fun (_v52 : (@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat)
  (@Bool)) (@List.{0} (@Bool))))) =>
(Sort 0)) _v49 (fun (_v52 : (@Unit)) =>
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@BodyIngress.machine _v0)) _v1 _v20) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@BodyIngress.machine _v0) _v1 _v20
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v50 _v51) _v46)
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)) _v1
  _v20 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@BodyIngress.machine _v0)) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v20) _v18 _v45) (fun (_v53 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v1 _v20))) =>
(@SerializedBody.image _v11 _v19 _v16 _v4 _v6 _v7 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v2 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) _v47 _v2)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 :
  Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v20) _v53)))))) (fun (_v52 : (@Nat)) =>
(fun (_v53 : (@Bool)) =>
(fun (_v54 : (@List.{0} (@Bool))) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v55 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v55 _v7) (@And (@Eq.{(0 + 1)} (@List.{0} (@Bool)) _v54 (@List.drop.{0} (@Bool)
  _v55 _v48)) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@BodyIngress.machine _v0)) _v1 _v20) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@BodyIngress.machine _v0) _v1 _v20
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v50 _v51) _v46)
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)) _v1
  _v20 (@BodyIngress.body _v0 (@SerializedBody.done _v53)) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v20) _v18
  _v45) (fun (_v56 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v20))) =>
(@SerializedBody.image _v11 _v19 _v16 _v4 _v6 _v7 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v2 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) _v47 _v2)) _v52 _v55 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v7 _v55) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v20)
  _v56)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @PhysicalCallerClosure.installed_body

-- Independent literal expected type for PhysicalCallerClosure.oldState.
noncomputable def PartACanonical.Types.p0566 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))),
(@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PhysicalCallerClosure.callerMachine _v0))))) := by
  exact @PhysicalCallerClosure.oldState

-- Independent literal expected type for PhysicalCallerClosure.old_rows.
noncomputable def PartACanonical.Types.p0567 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))),
(∀ (_v2 : (@Option.{0} (@Bool))),
(∀ (_v3 : (∀ (_v3 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))) _v1
  (@BodyIngress.body _v0 (@SerializedBody.entry _v3))))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@PhysicalCallerClosure.callerMachine _v0) (@PhysicalCallerClosure.oldState
  _v0 _v1) _v2) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))
  (@PhysicalCallerClosure.oldState _v0 (@Prod.fst.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@BodyIngress.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@BodyIngress.machine _v0) _v1 _v2))) (@Prod.snd.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@BodyIngress.machine _v0) _v1
  _v2)))))))) := by
  exact @PhysicalCallerClosure.old_rows

-- Complete literal proposition for PhysicalCallerClosure.old_rows; original proof reused.
theorem PartACanonical.Surface.m0333 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))),
(∀ (_v2 : (@Option.{0} (@Bool))),
(∀ (_v3 : (∀ (_v3 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))) _v1
  (@BodyIngress.body _v0 (@SerializedBody.entry _v3))))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@PhysicalCallerClosure.callerMachine _v0) (@PhysicalCallerClosure.oldState
  _v0 _v1) _v2) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))
  (@PhysicalCallerClosure.oldState _v0 (@Prod.fst.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@BodyIngress.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@BodyIngress.machine _v0) _v1 _v2))) (@Prod.snd.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@BodyIngress.machine _v0) _v1
  _v2)))))))) := by
  exact @PhysicalCallerClosure.old_rows

-- Independent literal expected type for PhysicalCallerClosure.old_rows_mirror.
noncomputable def PartACanonical.Types.p0568 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))),
(∀ (_v2 : (@Option.{0} (@Bool))),
(∀ (_v3 : (∀ (_v3 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))) _v1
  (@BodyIngress.body _v0 (@SerializedBody.entry _v3))))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@PhysicalCallerClosure.callerMachine _v0) (@PhysicalCallerClosure.oldState
  _v0 _v1) _v2) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))
  (@PhysicalCallerClosure.oldState _v0 (@Prod.fst.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@BodyIngress.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@BodyIngress.machine _v0) _v1 _v2))) (@Prod.snd.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@BodyIngress.machine _v0) _v1
  _v2)))))))) := by
  exact @PhysicalCallerClosure.old_rows_mirror

-- Complete literal proposition for PhysicalCallerClosure.old_rows_mirror; original proof reused.
theorem PartACanonical.Surface.m0334 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))),
(∀ (_v2 : (@Option.{0} (@Bool))),
(∀ (_v3 : (∀ (_v3 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))) _v1
  (@BodyIngress.body _v0 (@SerializedBody.entry _v3))))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@PhysicalCallerClosure.callerMachine _v0) (@PhysicalCallerClosure.oldState
  _v0 _v1) _v2) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PhysicalCallerClosure.callerMachine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))
  (@PhysicalCallerClosure.oldState _v0 (@Prod.fst.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@BodyIngress.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@BodyIngress.machine _v0) _v1 _v2))) (@Prod.snd.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@BodyIngress.machine _v0) _v1
  _v2)))))))) := by
  exact @PhysicalCallerClosure.old_rows_mirror
