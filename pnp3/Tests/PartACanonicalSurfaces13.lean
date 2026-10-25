import Tests.PartACanonicalABI
import Tests.PartAG2InterfaceTests

/-! Infrastructure: mechanical literal restatements of this exact original API.
Proof terms are reused; these are not independently authored correctness proofs.
Type pins, theorem mirrors and direct roots remain separate manifests. -/
set_option autoImplicit false

-- Independent literal expected type for StandardTMBridgeClosure.Target.Source.
noncomputable def PartACanonical.Types.p0756 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(Sort 0)))))) := by
  exact @StandardTMBridgeClosure.Target.Source

-- Independent literal expected type for StandardTMBridgeClosure.compile.
noncomputable def PartACanonical.Types.p0757 :
(∀ (_v0 : (@Pnp3.Complexity.Uniform.V1.UniformTM)),
(@Turing.TM0.Machine.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))))) := by
  exact @StandardTMBridgeClosure.compile

-- Independent literal expected type for StandardTMBridgeClosure.degree.
noncomputable def PartACanonical.Types.p0760 :
(∀ (_v0 : (@Nat)),
(@Nat)) := by
  exact @StandardTMBridgeClosure.degree

-- Independent literal expected type for StandardTMBridgeClosure.degree_bound.
noncomputable def PartACanonical.Types.p0761 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  (@Pnp3.Complexity.Uniform.V1.polyClock (@NormalClockClosure.degree _v0) _v1))) (@Pnp3.Complexity.Uniform.V1.polyClock
  (@StandardTMBridgeClosure.degree _v0) _v1)))) := by
  exact @StandardTMBridgeClosure.degree_bound

-- Complete literal proposition for StandardTMBridgeClosure.degree_bound; original proof reused.
theorem PartACanonical.Surface.m0453 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  (@Pnp3.Complexity.Uniform.V1.polyClock (@NormalClockClosure.degree _v0) _v1))) (@Pnp3.Complexity.Uniform.V1.polyClock
  (@StandardTMBridgeClosure.degree _v0) _v1)))) := by
  exact @StandardTMBridgeClosure.degree_bound

-- Independent literal expected type for StandardTMBridgeClosure.degree_bound_full.
noncomputable def PartACanonical.Types.p0762 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (4503599627370496 : Nat) (@instOfNatNat (4503599627370496 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))
  (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (4503599627370496 : Nat) (@instOfNatNat (4503599627370496 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))
  (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (4503599627370496 : Nat) (@instOfNatNat (4503599627370496 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))
  (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4503599627370496 : Nat) (@instOfNatNat
  (4503599627370496 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 :
  Nat))))) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))))) := by
  exact @StandardTMBridgeClosure.degree_bound_full

-- Complete literal proposition for StandardTMBridgeClosure.degree_bound_full; original proof reused.
theorem PartACanonical.Surface.m0454 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (4503599627370496 : Nat) (@instOfNatNat (4503599627370496 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))
  (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (4503599627370496 : Nat) (@instOfNatNat (4503599627370496 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))
  (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (4503599627370496 : Nat) (@instOfNatNat (4503599627370496 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))
  (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4503599627370496 : Nat) (@instOfNatNat
  (4503599627370496 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 :
  Nat))))) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))))) := by
  exact @StandardTMBridgeClosure.degree_bound_full

-- Independent literal expected type for StandardTMBridgeClosure.encode.
noncomputable def PartACanonical.Types.p0763 :
(∀ (_v0 : (@List.{0} (@Bool))),
(@List.{0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))))) := by
  exact @StandardTMBridgeClosure.encode

-- Independent literal expected type for StandardTMBridgeClosure.encode.eq_1.
noncomputable def PartACanonical.Types.p0764 :
(∀ (_v0 : (@List.{0} (@Bool))),
(@Eq.{(0 + 1)} (@List.{0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool)))) (@StandardTMBridgeClosure.encode _v0)
  (@List.map.{0, 0} (@Bool) (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (fun (_v1 : (@Bool)) =>
(@Prod.mk.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@Bool.false) (@Option.some.{0} (@Bool) _v1))) _v0))) := by
  exact @StandardTMBridgeClosure.encode.eq_1

-- Complete literal proposition for StandardTMBridgeClosure.encode.eq_1; original proof reused.
theorem PartACanonical.Surface.m0455 :
(∀ (_v0 : (@List.{0} (@Bool))),
(@Eq.{(0 + 1)} (@List.{0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool)))) (@StandardTMBridgeClosure.encode _v0)
  (@List.map.{0, 0} (@Bool) (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (fun (_v1 : (@Bool)) =>
(@Prod.mk.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@Bool.false) (@Option.some.{0} (@Bool) _v1))) _v0))) := by
  exact @StandardTMBridgeClosure.encode.eq_1

-- Independent literal expected type for StandardTMBridgeClosure.encode_injective.
noncomputable def PartACanonical.Types.p0765 :
(@Function.Injective.{(0 + 1), (0 + 1)} (@List.{0} (@Bool)) (@List.{0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))))
  (@StandardTMBridgeClosure.encode)) := by
  exact @StandardTMBridgeClosure.encode_injective

-- Complete literal proposition for StandardTMBridgeClosure.encode_injective; original proof reused.
theorem PartACanonical.Surface.m0456 :
(@Function.Injective.{(0 + 1), (0 + 1)} (@List.{0} (@Bool)) (@List.{0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))))
  (@StandardTMBridgeClosure.encode)) := by
  exact @StandardTMBridgeClosure.encode_injective

-- Independent literal expected type for StandardTMBridgeClosure.encode_injective_full.
noncomputable def PartACanonical.Types.p0766 :
(∀ (_v0 : (@List.{0} (@Bool))),
(∀ (_v1 : (@List.{0} (@Bool))),
(∀ (_v2 : (@Eq.{(0 + 1)} (@List.{0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool)))) (@StandardTMBridgeClosure.encode _v0)
  (@StandardTMBridgeClosure.encode _v1))),
(@Eq.{(0 + 1)} (@List.{0} (@Bool)) _v0 _v1)))) := by
  exact @StandardTMBridgeClosure.encode_injective_full

-- Complete literal proposition for StandardTMBridgeClosure.encode_injective_full; original proof reused.
theorem PartACanonical.Surface.m0457 :
(∀ (_v0 : (@List.{0} (@Bool))),
(∀ (_v1 : (@List.{0} (@Bool))),
(∀ (_v2 : (@Eq.{(0 + 1)} (@List.{0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool)))) (@StandardTMBridgeClosure.encode _v0)
  (@StandardTMBridgeClosure.encode _v1))),
(@Eq.{(0 + 1)} (@List.{0} (@Bool)) _v0 _v1)))) := by
  exact @StandardTMBridgeClosure.encode_injective_full

-- Independent literal expected type for StandardTMBridgeClosure.encoding.
noncomputable def PartACanonical.Types.p0767 :
(∀ (_v0 : (@List.{0} (@Bool))),
(@And (@Eq.{(0 + 1)} (@Nat) (@List.length.{0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool)))
  (@StandardTMBridgeClosure.encode _v0)) (@List.length.{0} (@Bool) _v0)) (@Eq.{(0 + 1)} (@List.{0} (@Bool)) (@List.map.{0,
  0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Bool) (fun (_v1 : (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool)))) =>
(@Option.getD.{0} (@Bool) (@Prod.snd.{0, 0} (@Bool) (@Option.{0} (@Bool)) _v1) (@Bool.false)))
  (@StandardTMBridgeClosure.encode _v0)) _v0))) := by
  exact @StandardTMBridgeClosure.encoding

-- Complete literal proposition for StandardTMBridgeClosure.encoding; original proof reused.
theorem PartACanonical.Surface.m0458 :
(∀ (_v0 : (@List.{0} (@Bool))),
(@And (@Eq.{(0 + 1)} (@Nat) (@List.length.{0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool)))
  (@StandardTMBridgeClosure.encode _v0)) (@List.length.{0} (@Bool) _v0)) (@Eq.{(0 + 1)} (@List.{0} (@Bool)) (@List.map.{0,
  0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Bool) (fun (_v1 : (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool)))) =>
(@Option.getD.{0} (@Bool) (@Prod.snd.{0, 0} (@Bool) (@Option.{0} (@Bool)) _v1) (@Bool.false)))
  (@StandardTMBridgeClosure.encode _v0)) _v0))) := by
  exact @StandardTMBridgeClosure.encoding

-- Independent literal expected type for StandardTMBridgeClosure.encoding_full.
noncomputable def PartACanonical.Types.p0768 :
(∀ (_v0 : (@List.{0} (@Bool))),
(@And (@Eq.{(0 + 1)} (@Nat) (@List.length.{0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool)))
  (@StandardTMBridgeClosure.encode _v0)) (@List.length.{0} (@Bool) _v0)) (@Eq.{(0 + 1)} (@List.{0} (@Bool)) (@List.map.{0,
  0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Bool) (fun (_v1 : (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool)))) =>
(@Option.getD.{0} (@Bool) (@Prod.snd.{0, 0} (@Bool) (@Option.{0} (@Bool)) _v1) (@Bool.false)))
  (@StandardTMBridgeClosure.encode _v0)) _v0))) := by
  exact @StandardTMBridgeClosure.encoding_full

-- Complete literal proposition for StandardTMBridgeClosure.encoding_full; original proof reused.
theorem PartACanonical.Surface.m0459 :
(∀ (_v0 : (@List.{0} (@Bool))),
(@And (@Eq.{(0 + 1)} (@Nat) (@List.length.{0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool)))
  (@StandardTMBridgeClosure.encode _v0)) (@List.length.{0} (@Bool) _v0)) (@Eq.{(0 + 1)} (@List.{0} (@Bool)) (@List.map.{0,
  0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Bool) (fun (_v1 : (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool)))) =>
(@Option.getD.{0} (@Bool) (@Prod.snd.{0, 0} (@Bool) (@Option.{0} (@Bool)) _v1) (@Bool.false)))
  (@StandardTMBridgeClosure.encode _v0)) _v0))) := by
  exact @StandardTMBridgeClosure.encoding_full

-- Independent literal expected type for StandardTMBridgeClosure.finite_control.
noncomputable def PartACanonical.Types.p0769 :
(∀ (_v0 : (@Pnp3.Complexity.Uniform.V1.UniformTM)),
(@And (@Eq.{(0 + 1)} (@Nat) (@Fintype.card.{0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@instFintypeProd.{0, 0}
  (@Bool) (@Option.{0} (@Bool)) (@Bool.fintype) (@instFintypeOption.{0} (@Bool) (@Bool.fintype)))) (@OfNat.ofNat.{0}
  (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) (@Eq.{(0 + 1)} (@Nat) (@Fintype.card.{0} (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instFintypeOption.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@instFintypeProd.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))) (@Fin.fintype (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin.fintype (@OfNat.ofNat.{0} (@Nat) (4
  : Nat) (@instOfNatNat (4 : Nat))))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)))))) := by
  exact @StandardTMBridgeClosure.finite_control

-- Complete literal proposition for StandardTMBridgeClosure.finite_control; original proof reused.
theorem PartACanonical.Surface.m0460 :
(∀ (_v0 : (@Pnp3.Complexity.Uniform.V1.UniformTM)),
(@And (@Eq.{(0 + 1)} (@Nat) (@Fintype.card.{0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@instFintypeProd.{0, 0}
  (@Bool) (@Option.{0} (@Bool)) (@Bool.fintype) (@instFintypeOption.{0} (@Bool) (@Bool.fintype)))) (@OfNat.ofNat.{0}
  (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) (@Eq.{(0 + 1)} (@Nat) (@Fintype.card.{0} (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instFintypeOption.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@instFintypeProd.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))) (@Fin.fintype (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin.fintype (@OfNat.ofNat.{0} (@Nat) (4
  : Nat) (@instOfNatNat (4 : Nat))))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)))))) := by
  exact @StandardTMBridgeClosure.finite_control

-- Independent literal expected type for StandardTMBridgeClosure.finite_control_full.
noncomputable def PartACanonical.Types.p0770 :
(∀ (_v0 : (@Pnp3.Complexity.Uniform.V1.UniformTM)),
(@And (@Eq.{(0 + 1)} (@Nat) (@Fintype.card.{0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@instFintypeProd.{0, 0}
  (@Bool) (@Option.{0} (@Bool)) (@Bool.fintype) (@instFintypeOption.{0} (@Bool) (@Bool.fintype)))) (@OfNat.ofNat.{0}
  (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) (@Eq.{(0 + 1)} (@Nat) (@Fintype.card.{0} (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instFintypeOption.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@instFintypeProd.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))) (@Fin.fintype (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin.fintype (@OfNat.ofNat.{0} (@Nat) (4
  : Nat) (@instOfNatNat (4 : Nat))))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)))))) := by
  exact @StandardTMBridgeClosure.finite_control_full

-- Complete literal proposition for StandardTMBridgeClosure.finite_control_full; original proof reused.
theorem PartACanonical.Surface.m0461 :
(∀ (_v0 : (@Pnp3.Complexity.Uniform.V1.UniformTM)),
(@And (@Eq.{(0 + 1)} (@Nat) (@Fintype.card.{0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@instFintypeProd.{0, 0}
  (@Bool) (@Option.{0} (@Bool)) (@Bool.fintype) (@instFintypeOption.{0} (@Bool) (@Bool.fintype)))) (@OfNat.ofNat.{0}
  (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) (@Eq.{(0 + 1)} (@Nat) (@Fintype.card.{0} (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instFintypeOption.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@instFintypeProd.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))) (@Fin.fintype (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin.fintype (@OfNat.ofNat.{0} (@Nat) (4
  : Nat) (@instOfNatNat (4 : Nat))))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)))))) := by
  exact @StandardTMBridgeClosure.finite_control_full

-- Independent literal expected type for StandardTMBridgeClosure.raw.
noncomputable def PartACanonical.Types.p0771 :
(∀ (_v0 : (@Nat)),
(@StandardTMBridgeClosure.Target.Raw _v0)) := by
  exact @StandardTMBridgeClosure.raw

-- Complete literal proposition for StandardTMBridgeClosure.raw; original proof reused.
theorem PartACanonical.Surface.m0462 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(let _v3 : (@Pnp3.Complexity.Uniform.V1.UniformTM) := (@NormalFinalClosure.machine2 _v0);
(let _v4 : (@Nat) := (@RawCallerClosure.allocation _v0 _v1);
(let _v5 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v3 _v1 _v4 _v2);
(let _v6 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool)))) := (@Turing.TM0.init.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) (@StandardTMBridgeClosure.encode (@List.ofFn.{0}
  (@Bool) _v1 _v2)));
(let _v7 : (∀ (_v7 : (@Bool)),
(@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2 _v0)))) := (fun (_v7 : (@Bool)) =>
(@NormalFinalClosure.old2 _v0 (@RawCallerClosure.old _v0 (@CertificateGuardClosure.old _v0 (@TotalIngressClosure.old _v0
  (@BodyIngress.old _v0 (@CarryWindow.embed _v0 (@CanonicalLeaf.result _v0 _v7))))))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v8 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v9 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool)))) (fun (_v10 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0}
  (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4
  : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))) =>
(@And (let _v11 : (@Nat) := (@RawCallerClosure.allocation _v0 _v1);
(let _v12 : (@Pnp3.Complexity.Uniform.V1.UniformTM) := (@NormalFinalClosure.machine2 _v0);
(let _v13 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v12) _v1 _v11) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v12 _v1 _v11 _v2);
(let _v14 : (@Pnp3.Complexity.Uniform.V1.UniformTM) := (@RawCallerClosure.machine _v0);
(let _v15 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v14) _v1 _v11) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v14 _v1 _v11 _v2);
(let _v16 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0))) :=
  (@RawCallerClosure.callerState _v0 (@PhysicalCallerClosure.rowsDone _v0));
(let _v17 : (∀ (_v17 : (@Bool)),
(@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0)))) := (fun (_v17 : (@Bool)) =>
(@RawCallerClosure.old _v0 (@CertificateGuardClosure.old _v0 (@TotalIngressClosure.old _v0 (@BodyIngress.old _v0
  (@CarryWindow.embed _v0 (@CanonicalLeaf.result _v0 _v17)))))));
(@And (@LE.le.{0} (@Nat) (@instLENat) _v8 _v9) (@And (@LE.le.{0} (@Nat) (@instLENat) _v9 (@HMul.hMul.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (17592186044416 : Nat) (@instOfNatNat (17592186044416 : Nat))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat))))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 :
  Nat)))))) (@And (∀ (_v18 : (@Nat)),
(∀ (_v19 : (@LE.le.{0} (@Nat) (@instLENat) _v18 _v8)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@NormalFinalClosure.machine2 _v0)) _v1 _v11) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@NormalFinalClosure.machine2
  _v0) _v1 _v11 _v18 _v13) (@NormalFinalClosure.config2 _v0 _v1 _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v14 _v1
  _v11 _v18 _v15))))) (@And (∀ (_v18 : (@Nat)),
(∀ (_v19 : (@LE.le.{0} (@Nat) (@instLENat) _v18 _v8)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v14)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v14) _v1 _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v14 _v1
  _v11 _v18 _v15)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v14)))) (@And (∀ (_v18 : (@Nat)),
(∀ (_v19 : (@LT.lt.{0} (@Nat) (@instLTNat) _v18 _v8)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v14))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v14) _v1 _v11
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v14 _v1 _v11 _v18 _v15)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject
  _v14)) (@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v14))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v14) _v1 _v11
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v14 _v1 _v11 _v18 _v15)) _v16) (∀ (_v20 : (@Bool)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v14)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v14) _v1 _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v14 _v1
  _v11 _v18 _v15)) (@_v17 _v20))))))) (@And (∀ (_v18 : (@Nat)),
(∀ (_v19 : (@LT.lt.{0} (@Nat) (@instLTNat) _v18 _v9)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2 _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@NormalFinalClosure.machine2 _v0)) _v1 _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@NormalFinalClosure.machine2
  _v0) _v1 _v11 _v18 _v13)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@NormalFinalClosure.machine2 _v0))) (@And
  (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2 _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@NormalFinalClosure.machine2 _v0)) _v1 _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@NormalFinalClosure.machine2
  _v0) _v1 _v11 _v18 _v13)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@NormalFinalClosure.machine2 _v0))) (∀ (_v20 :
  (@Bool)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2 _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@NormalFinalClosure.machine2 _v0)) _v1 _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@NormalFinalClosure.machine2
  _v0) _v1 _v11 _v18 _v13)) (@NormalFinalClosure.old2 _v0 (@_v17 _v20)))))))) (@Or (@And (@Eq.{(0 + 1)} (@Nat) _v9 _v8)
  (@And (@Exists.{(0 + 1)} (@Bool) (fun (_v18 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v14)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v14) _v1 _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v14 _v1
  _v11 _v8 _v15)) (@_v17 _v18)))) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2 _v0)) _v1 _v11)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@NormalFinalClosure.machine2 _v0) _v1 _v11 _v9 _v13)
  (@NormalFinalClosure.config2 _v0 _v1 _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v14 _v1 _v11 _v8 _v15))))) (@Or
  (@And (@Eq.{(0 + 1)} (@Nat) _v9 _v8) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v14))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v14) _v1 _v11
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v14 _v1 _v11 _v8 _v15)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v14))
  (@And (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.encodedRelationLanguage
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0) _v1 _v2) (@Bool.false)) (@Eq.{(0 +
  1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2
  _v0)) _v1 _v11) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@NormalFinalClosure.machine2 _v0) _v1 _v11 _v9 _v13)
  (@NormalFinalClosure.config2 _v0 _v1 _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v14 _v1 _v11 _v8 _v15))))))
  (@Exists.{(0 + 1)} (@Nat) (fun (_v18 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v19 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v18) (fun (_v20 : (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v18)) =>
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v19) (fun (_v21 : (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v19)) =>
(@Exists.{0} (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v18 _v19) _v1) (fun (_v22 :
  (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v18 _v19) _v1)) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.decodePair _v1 _v2) (@Option.some.{0} (@Prod.{0, 0} (@Sigma.{0, 0} (@Nat) (fun
  (_v23 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v23))) (@Sigma.{0, 0} (@Nat) (fun (_v23 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v23)))) (@Prod.mk.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v23 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v23))) (@Sigma.{0, 0} (@Nat) (fun (_v23 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v23))) (@Sigma.mk.{0, 0} (@Nat) (fun (_v23 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v23)) _v18 _v20) (@Sigma.mk.{0, 0} (@Nat) (fun (_v23 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v23)) _v19 _v21)))) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v1) _v2 (@Eq.rec.{(0 + 1), (0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v18 _v19) (fun (_v23 :
  (@Nat)) =>
(fun (_v24 : (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v18 _v19) _v23)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v23))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v18 _v19 _v20 _v21)
  _v1 _v22)) (@And (@Eq.{(0 + 1)} (@Nat) _v19 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v18 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Exists.{(0 + 1)} (@Nat) (fun (_v23
  : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v24 : (@Nat)) =>
(@And (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.tagMatches (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v18 _v19) (@Fin.append.{(0 + 1)} _v18 _v19 (@Bool) _v20 _v21))
  (@Bool.true)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Nat))
  (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros? (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v18 _v19) (@Fin.append.{(0 + 1)} _v18 _v19 (@Bool) _v20 _v21)) (@Option.some.{0}
  (@Nat) _v24)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Nat) (@Nat)))
  (@Pnp4.Frontier.ContractExpansion.contentHeader? (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v18 _v19) (@Fin.append.{(0 + 1)} _v18 _v19 (@Bool) _v20 _v21)) (@Option.some.{0} (@Prod.{0, 0} (@Nat)
  (@Nat)) (@Prod.mk.{0, 0} (@Nat) (@Nat) _v23 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v24) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))) (let _v25 :
  (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v18 _v19);
(let _v26 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v1);
(let _v27 : (@Nat) := (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v25 (@Min.min.{0}
  (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v24)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v23)) _v25));
(let _v28 : (@Nat) := (@Cursor.Target.W _v0 _v23);
(@And (@LT.lt.{0} (@Nat) (@instLTNat) (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v24))
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v23)) _v25) _v25) (@And (@LE.le.{0}
  (@Nat) (@instLENat) (@Pnp4.Frontier.ContractExpansion.bitLength _v23) _v27) (@And (@LE.le.{0} (@Nat) (@instLENat) _v28
  _v27) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v14))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v14) _v1 _v11
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v14 _v1 _v11 _v8 _v15)) _v16) (@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v25 _v24)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v23) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v11)) (fun (_v29 : (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v25 _v24)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v23) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v11))) =>
(@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v11)) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v14) _v1 _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v14 _v1
  _v11 _v8 _v15)) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v11) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v25 _v24) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))
  _v23) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v29)) (@Exists.{(0 + 1)} (@Bool) (fun (_v30 :
  (@Bool)) =>
(@And (@Eq.{(0 + 1)} (@Bool) _v30 (@Pnp3.Complexity.Uniform.V1.encodedRelationLanguage
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0) _v1 _v2)) (@And (@Eq.{(0 + 1)}
  (@Bool) _v30 (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v18 _v19 _v20 _v21))
  (@And (@Iff (@Eq.{(0 + 1)} (@Bool) _v30 (@Bool.true)) (@Exists.{(0 + 1)} (@Nat) (fun (_v31 : (@Nat)) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@Pnp4.Frontier.ContractExpansion.readNatBE (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v24)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v23))
  (@Pnp4.Frontier.ContractExpansion.bitLength _v28)) _v28) (@Pnp4.Frontier.ContractExpansion.padWord (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v18 _v19) (@Fin.append.{(0 + 1)} _v18 _v19 (@Bool) _v20 _v21)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat)
  (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v24)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v23)) (@Pnp4.Frontier.ContractExpansion.bitLength _v28)) _v28)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v24))
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v23))
  (@Pnp4.Frontier.ContractExpansion.bitLength _v28)) (@Option.some.{0} (@Nat) _v31)) (@And (@LE.le.{0} (@Nat) (@instLENat)
  _v31 _v28) (@And (∀ (_v32 : (@Nat)),
(∀ (_v33 : (@LT.lt.{0} (@Nat) (@instLTNat) _v32 _v31)),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v18 _v19) (@Fin.append.{(0 + 1)} _v18 _v19 (@Bool) _v20 _v21) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 :
  Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))) _v24)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v23))
  (@Pnp4.Frontier.ContractExpansion.bitLength _v28)) _v32)) (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v18 _v19) (@Fin.append.{(0 + 1)} _v18 _v19 (@Bool) _v20
  _v21) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v24)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v23))
  (@Pnp4.Frontier.ContractExpansion.bitLength _v28)) _v28) _v32))))) (∀ (_v32 : (@Nat)),
(∀ (_v33 : (@LE.le.{0} (@Nat) (@instLENat) _v31 _v32)),
(∀ (_v34 : (@LT.lt.{0} (@Nat) (@instLTNat) _v32 _v28)),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v18 _v19) (@Fin.append.{(0 + 1)} _v18 _v19 (@Bool) _v20 _v21) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 :
  Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))) _v24)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v23))
  (@Pnp4.Frontier.ContractExpansion.bitLength _v28)) _v32)) (@Bool.false))))))))))) (@Eq.{(0 + 1)}
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2
  _v0)) _v1 _v11) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@NormalFinalClosure.machine2 _v0) _v1 _v11 _v9 _v13)
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2
  _v0)) _v1 _v11 (@ite.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2
  _v0))) (@Eq.{(0 + 1)} (@Bool) _v30 (@Bool.true)) (@instDecidableEqBool _v30 (@Bool.true))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@NormalFinalClosure.machine2 _v0))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@NormalFinalClosure.machine2 _v0))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v11) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v25 _v24) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v23) (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v29) (@NormalFinalClosure.Target.cleared _v1 _v11
  (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v14) _v1 _v11
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v14 _v1 _v11 _v8 _v15)) _v26 _v27
  _v23)))))))))))))))))))))))))))))))))))))))))))))))))))))) (@And (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v9)) (@Pnp3.Complexity.Uniform.V1.polyClock (@StandardTMBridgeClosure.degree _v0) _v1))
  (@And (@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))))) (@StandardTMBridgeClosure.steps _v3 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v9)) _v6) (@Option.some.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool)))) _v10)) (@And (@And (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))) _v10) (@Option.some.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@Prod.mk.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4 _v9 _v5)) (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))
  (@PartACanonical.PrivateABI.a0050) (0 : Nat)))))) (∀ (_v11 : (@Int)),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Turing.Tape.nth.{0} (@Prod.{0, 0} (@Bool) (@Option.{0}
  (@Bool))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))) (@Turing.TM0.Cfg.Tape.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))) _v10) _v11) (@dite.{(0 + 1)} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@And (@LE.le.{0} (@Int)
  (@Int.instLEInt) (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int)
  (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v9 _v5)))) _v11)) (@LT.lt.{0} (@Int) (@Int.instLTInt) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int)
  (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4 _v9 _v5)))) _v11) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)))) (@instDecidableAnd (@LE.le.{0} (@Int) (@Int.instLEInt)
  (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0}
  (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1
  _v4) (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4 _v9 _v5)))) _v11)) (@LT.lt.{0} (@Int) (@Int.instLTInt)
  (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v9 _v5)))) _v11) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4))) (@Int.decLe
  (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0}
  (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1
  _v4) (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4 _v9 _v5)))) _v11)) (@Int.decLt (@HAdd.hAdd.{0, 0, 0} (@Int)
  (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v9 _v5)))) _v11) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)))) (fun (_v12
  : (@And (@LE.le.{0} (@Int) (@Int.instLEInt) (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0,
  0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v9 _v5)))) _v11)) (@LT.lt.{0} (@Int) (@Int.instLTInt) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int)
  (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4 _v9 _v5)))) _v11) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4))))) =>
(@Prod.mk.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@Decidable.decide (@Eq.{(0 + 1)} (@Int) (@HAdd.hAdd.{0, 0, 0} (@Int)
  (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v9 _v5)))) _v11) (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat)))) (@Int.instDecidableEq (@HAdd.hAdd.{0, 0,
  0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v9 _v5)))) _v11) (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))))) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v9 _v5) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Int.toNat (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int)
  (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v9 _v5)))) _v11)) (@StandardTMBridgeClosure.Represents._proof_2 _v3 _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  _v3 _v1 _v4 _v9 _v5) _v11 _v12))))) (fun (_v12 : (@Not (@And (@LE.le.{0} (@Int) (@Int.instLEInt) (@OfNat.ofNat.{0}
  (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int)
  (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4 _v9 _v5)))) _v11)) (@LT.lt.{0} (@Int) (@Int.instLTInt)
  (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v9 _v5)))) _v11) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)))))) =>
(@Prod.mk.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@Bool.false) (@Option.none.{0} (@Bool)))))))) (@And (∀ (_v11 : (@Nat)),
(∀ (_v12 : (@LE.le.{0} (@Nat) (@instLENat) _v11 _v9)),
(@Exists.{(0 + 1)} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool)))) (fun (_v13 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0}
  (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4
  : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))))) (@StandardTMBridgeClosure.steps _v3 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v11)) _v6) (@Option.some.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool)))) _v13)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))) _v13) (@Option.some.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@Prod.mk.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4 _v11 _v5)) (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))
  (@PartACanonical.PrivateABI.a0050) (0 : Nat)))))) (∀ (_v14 : (@Int)),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Turing.Tape.nth.{0} (@Prod.{0, 0} (@Bool) (@Option.{0}
  (@Bool))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))) (@Turing.TM0.Cfg.Tape.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))) _v13) _v14) (@dite.{(0 + 1)} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@And (@LE.le.{0} (@Int)
  (@Int.instLEInt) (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int)
  (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v11 _v5)))) _v14)) (@LT.lt.{0} (@Int) (@Int.instLTInt) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int)
  (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4 _v11 _v5)))) _v14) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)))) (@instDecidableAnd (@LE.le.{0} (@Int) (@Int.instLEInt)
  (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0}
  (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1
  _v4) (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4 _v11 _v5)))) _v14)) (@LT.lt.{0} (@Int) (@Int.instLTInt)
  (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v11 _v5)))) _v14) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)))
  (@Int.decLe (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int)
  (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v11 _v5)))) _v14)) (@Int.decLt (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd))
  (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4 _v11 _v5)))) _v14) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)))) (fun (_v15 : (@And (@LE.le.{0} (@Int) (@Int.instLEInt)
  (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0}
  (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1
  _v4) (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4 _v11 _v5)))) _v14)) (@LT.lt.{0} (@Int) (@Int.instLTInt)
  (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v11 _v5)))) _v14) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4))))) =>
(@Prod.mk.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@Decidable.decide (@Eq.{(0 + 1)} (@Int) (@HAdd.hAdd.{0, 0, 0} (@Int)
  (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v11 _v5)))) _v14) (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat)))) (@Int.instDecidableEq (@HAdd.hAdd.{0, 0,
  0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v11 _v5)))) _v14) (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))))) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v11 _v5) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Int.toNat (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int)
  (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v11 _v5)))) _v14)) (@StandardTMBridgeClosure.Represents._proof_2 _v3 _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  _v3 _v1 _v4 _v11 _v5) _v14 _v15))))) (fun (_v15 : (@Not (@And (@LE.le.{0} (@Int) (@Int.instLEInt) (@OfNat.ofNat.{0}
  (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int)
  (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4 _v11 _v5)))) _v14)) (@LT.lt.{0} (@Int) (@Int.instLTInt)
  (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v11 _v5)))) _v14) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)))))) =>
(@Prod.mk.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@Bool.false) (@Option.none.{0} (@Bool))))))))))))) (@And (∀ (_v11 :
  (@Nat)),
(∀ (_v12 : (@LE.le.{0} (@Nat) (@instLENat) _v11 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v9)))),
(@Exists.{(0 + 1)} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool)))) (fun (_v13 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0}
  (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4
  : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0,
  0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat
  (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))) (@StandardTMBridgeClosure.steps _v3 _v11 _v6) (@Option.some.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0}
  (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3))
  (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool)))) _v13)))))) (@And (∀ (_v11 : (@Nat)),
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) _v11 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v9)))),
(∀ (_v13 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))),
(∀ (_v14 : (@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))))) (@StandardTMBridgeClosure.steps _v3 _v11 _v6) (@Option.some.{0}
  (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool)))) _v13))),
(@And (@Ne.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool)
  (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) _v13) (@Option.some.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v3) (@OfNat.ofNat.{0} (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat))) (@StandardTMBridgeClosure.Target.Simulation._proof_1) (0 : Nat)))))) (@And (@Ne.{(0 +
  1)} (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0}
  (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool)))
  (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))) _v13) (@Option.some.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v3) (@OfNat.ofNat.{0} (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat))) (@StandardTMBridgeClosure.Target.Simulation._proof_1) (0 : Nat)))))) (∀ (_v15 :
  (@Bool)),
(@Ne.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool)
  (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) _v13) (@Option.some.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))) (@_v7 _v15) (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))
  (@StandardTMBridgeClosure.Target.Simulation._proof_1) (0 : Nat))))))))))))) (@Or (@Exists.{(0 + 1)} (@Bool) (fun (_v11 :
  (@Bool)) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool)
  (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) _v10) (@Option.some.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2 _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4
  : Nat) (@instOfNatNat (4 : Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@NormalFinalClosure.machine2 _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@_v7 _v11)
  (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@StandardTMBridgeClosure.Target.Simulation._proof_1) (0 :
  Nat)))))) (@Ne.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))))) (@Turing.TM0.step.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))) (@StandardTMBridgeClosure.compile _v3) _v10) (@Option.none.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool)
  (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))))))))) (@Exists.{(0 + 1)} (@Bool) (fun (_v11 : (@Bool))
  =>
(@And (@Eq.{(0 + 1)} (@Bool) _v11 (@Pnp3.Complexity.Uniform.V1.encodedRelationLanguage
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0) _v1 _v2)) (@And (@Eq.{(0 + 1)}
  (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool)))
  (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))) _v10) (@Option.some.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))) (@ite.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3))
  (@Eq.{(0 + 1)} (@Bool) _v11 (@Bool.true)) (@instDecidableEqBool _v11 (@Bool.true))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v3) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v3)) (@OfNat.ofNat.{0}
  (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat))) (@StandardTMBridgeClosure.Target.Simulation._proof_1) (0 : Nat)))))) (@Eq.{(0 + 1)}
  (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))) (@Turing.TM0.step.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) (@StandardTMBridgeClosure.compile _v3) _v10)
  (@Option.none.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool)))))))))))))))))))))))))))))))) := by
  exact @StandardTMBridgeClosure.raw

-- Independent literal expected type for StandardTMBridgeClosure.raw_full.
noncomputable def PartACanonical.Types.p0772 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(let _v3 : (@Pnp3.Complexity.Uniform.V1.UniformTM) := (@NormalFinalClosure.machine2 _v0);
(let _v4 : (@Nat) := (@RawCallerClosure.allocation _v0 _v1);
(let _v5 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v3 _v1 _v4 _v2);
(let _v6 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool)))) := (@Turing.TM0.init.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) (@StandardTMBridgeClosure.encode (@List.ofFn.{0}
  (@Bool) _v1 _v2)));
(let _v7 : (∀ (_v7 : (@Bool)),
(@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2 _v0)))) := (fun (_v7 : (@Bool)) =>
(@NormalFinalClosure.old2 _v0 (@RawCallerClosure.old _v0 (@CertificateGuardClosure.old _v0 (@TotalIngressClosure.old _v0
  (@BodyIngress.old _v0 (@CarryWindow.embed _v0 (@CanonicalLeaf.result _v0 _v7))))))));
(let _v8 : (@Pnp3.Complexity.Uniform.V1.UniformTM) := (@RawCallerClosure.machine _v0);
(let _v9 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v8) _v1 _v4) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v8 _v1 _v4 _v2);
(let _v10 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0))) :=
  (@RawCallerClosure.callerState _v0 (@PhysicalCallerClosure.rowsDone _v0));
(let _v11 : (∀ (_v11 : (@Bool)),
(@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0)))) := (fun (_v11 : (@Bool)) =>
(@RawCallerClosure.old _v0 (@CertificateGuardClosure.old _v0 (@TotalIngressClosure.old _v0 (@BodyIngress.old _v0
  (@CarryWindow.embed _v0 (@CanonicalLeaf.result _v0 _v11)))))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v12 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v13 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool)))) (fun (_v14 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0}
  (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4
  : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))) =>
(@And (@And (@LE.le.{0} (@Nat) (@instLENat) _v12 _v13) (@And (@LE.le.{0} (@Nat) (@instLENat) _v13 (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (17592186044416 : Nat) (@instOfNatNat (17592186044416 : Nat)))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat)
  (@instOfNatNat (8 : Nat)))))) (@And (∀ (_v15 : (@Nat)),
(∀ (_v16 : (@LE.le.{0} (@Nat) (@instLENat) _v15 _v12)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@NormalFinalClosure.machine2 _v0)) _v1 _v4) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@NormalFinalClosure.machine2
  _v0) _v1 _v4 _v15 _v5) (@NormalFinalClosure.config2 _v0 _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v8 _v1 _v4
  _v15 _v9))))) (@And (∀ (_v15 : (@Nat)),
(∀ (_v16 : (@LE.le.{0} (@Nat) (@instLENat) _v15 _v12)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v8)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v8) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v8 _v1 _v4
  _v15 _v9)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v8)))) (@And (∀ (_v15 : (@Nat)),
(∀ (_v16 : (@LT.lt.{0} (@Nat) (@instLTNat) _v15 _v12)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v8))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v8) _v1 _v4
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v8 _v1 _v4 _v15 _v9)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v8))
  (@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v8))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v8) _v1 _v4
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v8 _v1 _v4 _v15 _v9)) _v10) (∀ (_v17 : (@Bool)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v8)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v8) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v8 _v1 _v4
  _v15 _v9)) (@_v11 _v17))))))) (@And (∀ (_v15 : (@Nat)),
(∀ (_v16 : (@LT.lt.{0} (@Nat) (@instLTNat) _v15 _v13)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2 _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@NormalFinalClosure.machine2 _v0)) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@NormalFinalClosure.machine2
  _v0) _v1 _v4 _v15 _v5)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@NormalFinalClosure.machine2 _v0))) (@And
  (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2 _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@NormalFinalClosure.machine2 _v0)) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@NormalFinalClosure.machine2
  _v0) _v1 _v4 _v15 _v5)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@NormalFinalClosure.machine2 _v0))) (∀ (_v17 :
  (@Bool)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2 _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@NormalFinalClosure.machine2 _v0)) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@NormalFinalClosure.machine2
  _v0) _v1 _v4 _v15 _v5)) (@NormalFinalClosure.old2 _v0 (@_v11 _v17)))))))) (@Or (@And (@Eq.{(0 + 1)} (@Nat) _v13 _v12)
  (@And (@Exists.{(0 + 1)} (@Bool) (fun (_v15 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v8)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v8) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v8 _v1 _v4
  _v12 _v9)) (@_v11 _v15)))) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2 _v0)) _v1 _v4)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@NormalFinalClosure.machine2 _v0) _v1 _v4 _v13 _v5)
  (@NormalFinalClosure.config2 _v0 _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v8 _v1 _v4 _v12 _v9))))) (@Or (@And
  (@Eq.{(0 + 1)} (@Nat) _v13 _v12) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v8))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v8) _v1 _v4
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v8 _v1 _v4 _v12 _v9)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v8))
  (@And (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.encodedRelationLanguage
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0) _v1 _v2) (@Bool.false)) (@Eq.{(0 +
  1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2
  _v0)) _v1 _v4) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@NormalFinalClosure.machine2 _v0) _v1 _v4 _v13 _v5)
  (@NormalFinalClosure.config2 _v0 _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v8 _v1 _v4 _v12 _v9))))))
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
  _v1 _v19)) (@And (@Eq.{(0 + 1)} (@Nat) _v16 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v15 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Exists.{(0 + 1)} (@Nat) (fun (_v20
  : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v21 : (@Nat)) =>
(@And (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.tagMatches (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v15 _v16) (@Fin.append.{(0 + 1)} _v15 _v16 (@Bool) _v17 _v18))
  (@Bool.true)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Nat))
  (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros? (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v15 _v16) (@Fin.append.{(0 + 1)} _v15 _v16 (@Bool) _v17 _v18)) (@Option.some.{0}
  (@Nat) _v21)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Nat) (@Nat)))
  (@Pnp4.Frontier.ContractExpansion.contentHeader? (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v15 _v16) (@Fin.append.{(0 + 1)} _v15 _v16 (@Bool) _v17 _v18)) (@Option.some.{0} (@Prod.{0, 0} (@Nat)
  (@Nat)) (@Prod.mk.{0, 0} (@Nat) (@Nat) _v20 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v21) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))) (let _v22 :
  (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v15 _v16);
(let _v23 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v1);
(let _v24 : (@Nat) := (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v22 (@Min.min.{0}
  (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v21)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v20)) _v22));
(let _v25 : (@Nat) := (@Cursor.Target.W _v0 _v20);
(@And (@LT.lt.{0} (@Nat) (@instLTNat) (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v21))
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v20)) _v22) _v22) (@And (@LE.le.{0}
  (@Nat) (@instLENat) (@Pnp4.Frontier.ContractExpansion.bitLength _v20) _v24) (@And (@LE.le.{0} (@Nat) (@instLENat) _v25
  _v24) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v8))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v8) _v1 _v4
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v8 _v1 _v4 _v12 _v9)) _v10) (@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v22 _v21)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v20) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)) (fun (_v26 : (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v22 _v21)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v20) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4))) =>
(@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v8) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v8 _v1 _v4
  _v12 _v9)) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v22 _v21) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))
  _v20) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v26)) (@Exists.{(0 + 1)} (@Bool) (fun (_v27 :
  (@Bool)) =>
(@And (@Eq.{(0 + 1)} (@Bool) _v27 (@Pnp3.Complexity.Uniform.V1.encodedRelationLanguage
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0) _v1 _v2)) (@And (@Eq.{(0 + 1)}
  (@Bool) _v27 (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v15 _v16 _v17 _v18))
  (@And (@Iff (@Eq.{(0 + 1)} (@Bool) _v27 (@Bool.true)) (@Exists.{(0 + 1)} (@Nat) (fun (_v28 : (@Nat)) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@Pnp4.Frontier.ContractExpansion.readNatBE (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v21)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v20))
  (@Pnp4.Frontier.ContractExpansion.bitLength _v25)) _v25) (@Pnp4.Frontier.ContractExpansion.padWord (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v15 _v16) (@Fin.append.{(0 + 1)} _v15 _v16 (@Bool) _v17 _v18)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat)
  (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v21)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v20)) (@Pnp4.Frontier.ContractExpansion.bitLength _v25)) _v25)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v21))
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v20))
  (@Pnp4.Frontier.ContractExpansion.bitLength _v25)) (@Option.some.{0} (@Nat) _v28)) (@And (@LE.le.{0} (@Nat) (@instLENat)
  _v28 _v25) (@And (∀ (_v29 : (@Nat)),
(∀ (_v30 : (@LT.lt.{0} (@Nat) (@instLTNat) _v29 _v28)),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v15 _v16) (@Fin.append.{(0 + 1)} _v15 _v16 (@Bool) _v17 _v18) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 :
  Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))) _v21)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v20))
  (@Pnp4.Frontier.ContractExpansion.bitLength _v25)) _v29)) (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v15 _v16) (@Fin.append.{(0 + 1)} _v15 _v16 (@Bool) _v17
  _v18) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v21)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v20))
  (@Pnp4.Frontier.ContractExpansion.bitLength _v25)) _v25) _v29))))) (∀ (_v29 : (@Nat)),
(∀ (_v30 : (@LE.le.{0} (@Nat) (@instLENat) _v28 _v29)),
(∀ (_v31 : (@LT.lt.{0} (@Nat) (@instLTNat) _v29 _v25)),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v15 _v16) (@Fin.append.{(0 + 1)} _v15 _v16 (@Bool) _v17 _v18) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 :
  Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))) _v21)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v20))
  (@Pnp4.Frontier.ContractExpansion.bitLength _v25)) _v29)) (@Bool.false))))))))))) (@Eq.{(0 + 1)}
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2
  _v0)) _v1 _v4) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@NormalFinalClosure.machine2 _v0) _v1 _v4 _v13 _v5)
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2
  _v0)) _v1 _v4 (@ite.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2
  _v0))) (@Eq.{(0 + 1)} (@Bool) _v27 (@Bool.true)) (@instDecidableEqBool _v27 (@Bool.true))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@NormalFinalClosure.machine2 _v0))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@NormalFinalClosure.machine2 _v0))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v22 _v21) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v20) (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v26) (@NormalFinalClosure.Target.cleared _v1 _v4
  (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v8) _v1 _v4
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v8 _v1 _v4 _v12 _v9)) _v23 _v24
  _v20))))))))))))))))))))))))))))))))))))))))))))))) (@And (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v13)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) _v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4503599627370496 : Nat) (@instOfNatNat
  (4503599627370496 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 :
  Nat))))) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (4503599627370496 : Nat) (@instOfNatNat (4503599627370496 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))
  (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool)))
  (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))))) (@StandardTMBridgeClosure.steps _v3 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v13)) _v6) (@Option.some.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool)))) _v14)) (@And (@And (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))) _v14) (@Option.some.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@Prod.mk.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4 _v13 _v5)) (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))
  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (0 : Nat)))))) (∀ (_v15 : (@Int)),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Turing.Tape.nth.{0} (@Prod.{0, 0} (@Bool) (@Option.{0}
  (@Bool))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))) (@Turing.TM0.Cfg.Tape.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))) _v14) _v15) (@dite.{(0 + 1)} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@And (@LE.le.{0} (@Int)
  (@Int.instLEInt) (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int)
  (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v13 _v5)))) _v15)) (@LT.lt.{0} (@Int) (@Int.instLTInt) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int)
  (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4 _v13 _v5)))) _v15) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)))) (@instDecidableAnd (@LE.le.{0} (@Int) (@Int.instLEInt)
  (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0}
  (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1
  _v4) (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4 _v13 _v5)))) _v15)) (@LT.lt.{0} (@Int) (@Int.instLTInt)
  (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v13 _v5)))) _v15) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)))
  (@Int.decLe (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int)
  (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v13 _v5)))) _v15)) (@Int.decLt (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd))
  (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4 _v13 _v5)))) _v15) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)))) (fun (_v16 : (@And (@LE.le.{0} (@Int) (@Int.instLEInt)
  (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0}
  (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1
  _v4) (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4 _v13 _v5)))) _v15)) (@LT.lt.{0} (@Int) (@Int.instLTInt)
  (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v13 _v5)))) _v15) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4))))) =>
(@Prod.mk.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@Decidable.decide (@Eq.{(0 + 1)} (@Int) (@HAdd.hAdd.{0, 0, 0} (@Int)
  (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v13 _v5)))) _v15) (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat)))) (@Int.instDecidableEq (@HAdd.hAdd.{0, 0,
  0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v13 _v5)))) _v15) (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))))) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v13 _v5) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Int.toNat (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int)
  (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v13 _v5)))) _v15)) (@Decidable.byContradiction (@LT.lt.{0} (@Nat) (@instLTNat) (@Int.toNat (@HAdd.hAdd.{0, 0, 0} (@Int)
  (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v13 _v5)))) _v15)) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)) (@Nat.decLt (@Int.toNat (@HAdd.hAdd.{0, 0, 0}
  (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v13 _v5)))) _v15)) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)) (fun (_v17 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat)
  (@Int.toNat (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int)
  (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v13 _v5)))) _v15)) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)))) =>
(@StandardTMBridgeClosure.raw_full._proof_1 _v0 _v1 _v2 _v13 _v15 _v16 _v17))))))) (fun (_v16 : (@Not (@And (@LE.le.{0}
  (@Int) (@Int.instLEInt) (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int)
  (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v13 _v5)))) _v15)) (@LT.lt.{0} (@Int) (@Int.instLTInt) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int)
  (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4 _v13 _v5)))) _v15) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)))))) =>
(@Prod.mk.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@Bool.false) (@Option.none.{0} (@Bool)))))))) (@And (∀ (_v15 : (@Nat)),
(∀ (_v16 : (@LE.le.{0} (@Nat) (@instLENat) _v15 _v13)),
(@Exists.{(0 + 1)} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool)))) (fun (_v17 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0}
  (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4
  : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))))) (@StandardTMBridgeClosure.steps _v3 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v15)) _v6) (@Option.some.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool)))) _v17)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))) _v17) (@Option.some.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@Prod.mk.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4 _v15 _v5)) (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))
  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (0 : Nat)))))) (∀ (_v18 : (@Int)),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Turing.Tape.nth.{0} (@Prod.{0, 0} (@Bool) (@Option.{0}
  (@Bool))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))) (@Turing.TM0.Cfg.Tape.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))) _v17) _v18) (@dite.{(0 + 1)} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@And (@LE.le.{0} (@Int)
  (@Int.instLEInt) (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int)
  (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v15 _v5)))) _v18)) (@LT.lt.{0} (@Int) (@Int.instLTInt) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int)
  (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4 _v15 _v5)))) _v18) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)))) (@instDecidableAnd (@LE.le.{0} (@Int) (@Int.instLEInt)
  (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0}
  (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1
  _v4) (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4 _v15 _v5)))) _v18)) (@LT.lt.{0} (@Int) (@Int.instLTInt)
  (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v15 _v5)))) _v18) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)))
  (@Int.decLe (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int)
  (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v15 _v5)))) _v18)) (@Int.decLt (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd))
  (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4 _v15 _v5)))) _v18) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)))) (fun (_v19 : (@And (@LE.le.{0} (@Int) (@Int.instLEInt)
  (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0}
  (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1
  _v4) (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4 _v15 _v5)))) _v18)) (@LT.lt.{0} (@Int) (@Int.instLTInt)
  (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v15 _v5)))) _v18) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4))))) =>
(@Prod.mk.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@Decidable.decide (@Eq.{(0 + 1)} (@Int) (@HAdd.hAdd.{0, 0, 0} (@Int)
  (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v15 _v5)))) _v18) (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat)))) (@Int.instDecidableEq (@HAdd.hAdd.{0, 0,
  0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v15 _v5)))) _v18) (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))))) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v15 _v5) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Int.toNat (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int)
  (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v15 _v5)))) _v18)) (@Decidable.byContradiction (@LT.lt.{0} (@Nat) (@instLTNat) (@Int.toNat (@HAdd.hAdd.{0, 0, 0} (@Int)
  (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v15 _v5)))) _v18)) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)) (@Nat.decLt (@Int.toNat (@HAdd.hAdd.{0, 0, 0}
  (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v15 _v5)))) _v18)) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)) (fun (_v20 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat)
  (@Int.toNat (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int)
  (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v15 _v5)))) _v18)) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)))) =>
(@StandardTMBridgeClosure.raw_full._proof_1 _v0 _v1 _v2 _v15 _v18 _v19 _v20))))))) (fun (_v19 : (@Not (@And (@LE.le.{0}
  (@Int) (@Int.instLEInt) (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int)
  (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v15 _v5)))) _v18)) (@LT.lt.{0} (@Int) (@Int.instLTInt) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int)
  (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4 _v15 _v5)))) _v18) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)))))) =>
(@Prod.mk.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@Bool.false) (@Option.none.{0} (@Bool))))))))))))) (@And (∀ (_v15 :
  (@Nat)),
(∀ (_v16 : (@LE.le.{0} (@Nat) (@instLENat) _v15 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v13)))),
(@Exists.{(0 + 1)} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool)))) (fun (_v17 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0}
  (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4
  : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0,
  0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat
  (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))) (@StandardTMBridgeClosure.steps _v3 _v15 _v6) (@Option.some.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0}
  (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3))
  (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool)))) _v17)))))) (@And (∀ (_v15 : (@Nat)),
(∀ (_v16 : (@LT.lt.{0} (@Nat) (@instLTNat) _v15 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v13)))),
(∀ (_v17 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))),
(∀ (_v18 : (@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))))) (@StandardTMBridgeClosure.steps _v3 _v15 _v6) (@Option.some.{0}
  (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool)))) _v17))),
(@And (@Ne.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool)
  (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) _v17) (@Option.some.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v3) (@OfNat.ofNat.{0} (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (0 :
  Nat)))))) (@And (@Ne.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3))
  (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool)
  (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) _v17) (@Option.some.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v3) (@OfNat.ofNat.{0} (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (0 :
  Nat)))))) (∀ (_v19 : (@Bool)),
(@Ne.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool)
  (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) _v17) (@Option.some.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))) (@_v7 _v19) (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))
  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (0 : Nat))))))))))))) (@Or
  (@Exists.{(0 + 1)} (@Bool) (fun (_v15 : (@Bool)) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool)
  (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) _v14) (@Option.some.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2 _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4
  : Nat) (@instOfNatNat (4 : Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@NormalFinalClosure.machine2 _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@_v7 _v15)
  (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (0 : Nat)))))) (@Ne.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool)
  (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))))) (@Turing.TM0.step.{0, 0} (@Prod.{0, 0} (@Bool)
  (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))) (@StandardTMBridgeClosure.compile _v3) _v14) (@Option.none.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool)
  (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))))))))) (@Exists.{(0 + 1)} (@Bool) (fun (_v15 : (@Bool))
  =>
(@And (@Eq.{(0 + 1)} (@Bool) _v15 (@Pnp3.Complexity.Uniform.V1.encodedRelationLanguage
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0) _v1 _v2)) (@And (@Eq.{(0 + 1)}
  (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool)))
  (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))) _v14) (@Option.some.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))) (@ite.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3))
  (@Eq.{(0 + 1)} (@Bool) _v15 (@Bool.true)) (@instDecidableEqBool _v15 (@Bool.true))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v3) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v3)) (@OfNat.ofNat.{0}
  (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))
  (0 : Nat)))))) (@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool)))
  (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))))) (@Turing.TM0.step.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))) (@StandardTMBridgeClosure.compile _v3) _v14) (@Option.none.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool)
  (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool)))))))))))))))))))))))))))))))))))) := by
  exact @StandardTMBridgeClosure.raw_full

-- Complete literal proposition for StandardTMBridgeClosure.raw_full; original proof reused.
theorem PartACanonical.Surface.m0463 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(let _v3 : (@Pnp3.Complexity.Uniform.V1.UniformTM) := (@NormalFinalClosure.machine2 _v0);
(let _v4 : (@Nat) := (@RawCallerClosure.allocation _v0 _v1);
(let _v5 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v3 _v1 _v4 _v2);
(let _v6 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool)))) := (@Turing.TM0.init.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) (@StandardTMBridgeClosure.encode (@List.ofFn.{0}
  (@Bool) _v1 _v2)));
(let _v7 : (∀ (_v7 : (@Bool)),
(@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2 _v0)))) := (fun (_v7 : (@Bool)) =>
(@NormalFinalClosure.old2 _v0 (@RawCallerClosure.old _v0 (@CertificateGuardClosure.old _v0 (@TotalIngressClosure.old _v0
  (@BodyIngress.old _v0 (@CarryWindow.embed _v0 (@CanonicalLeaf.result _v0 _v7))))))));
(let _v8 : (@Pnp3.Complexity.Uniform.V1.UniformTM) := (@RawCallerClosure.machine _v0);
(let _v9 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v8) _v1 _v4) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v8 _v1 _v4 _v2);
(let _v10 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0))) :=
  (@RawCallerClosure.callerState _v0 (@PhysicalCallerClosure.rowsDone _v0));
(let _v11 : (∀ (_v11 : (@Bool)),
(@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@RawCallerClosure.machine _v0)))) := (fun (_v11 : (@Bool)) =>
(@RawCallerClosure.old _v0 (@CertificateGuardClosure.old _v0 (@TotalIngressClosure.old _v0 (@BodyIngress.old _v0
  (@CarryWindow.embed _v0 (@CanonicalLeaf.result _v0 _v11)))))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v12 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v13 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool)))) (fun (_v14 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0}
  (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4
  : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))) =>
(@And (@And (@LE.le.{0} (@Nat) (@instLENat) _v12 _v13) (@And (@LE.le.{0} (@Nat) (@instLENat) _v13 (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (17592186044416 : Nat) (@instOfNatNat (17592186044416 : Nat)))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat)
  (@instOfNatNat (8 : Nat)))))) (@And (∀ (_v15 : (@Nat)),
(∀ (_v16 : (@LE.le.{0} (@Nat) (@instLENat) _v15 _v12)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@NormalFinalClosure.machine2 _v0)) _v1 _v4) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@NormalFinalClosure.machine2
  _v0) _v1 _v4 _v15 _v5) (@NormalFinalClosure.config2 _v0 _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v8 _v1 _v4
  _v15 _v9))))) (@And (∀ (_v15 : (@Nat)),
(∀ (_v16 : (@LE.le.{0} (@Nat) (@instLENat) _v15 _v12)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v8)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v8) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v8 _v1 _v4
  _v15 _v9)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v8)))) (@And (∀ (_v15 : (@Nat)),
(∀ (_v16 : (@LT.lt.{0} (@Nat) (@instLTNat) _v15 _v12)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v8))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v8) _v1 _v4
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v8 _v1 _v4 _v15 _v9)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v8))
  (@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v8))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v8) _v1 _v4
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v8 _v1 _v4 _v15 _v9)) _v10) (∀ (_v17 : (@Bool)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v8)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v8) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v8 _v1 _v4
  _v15 _v9)) (@_v11 _v17))))))) (@And (∀ (_v15 : (@Nat)),
(∀ (_v16 : (@LT.lt.{0} (@Nat) (@instLTNat) _v15 _v13)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2 _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@NormalFinalClosure.machine2 _v0)) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@NormalFinalClosure.machine2
  _v0) _v1 _v4 _v15 _v5)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@NormalFinalClosure.machine2 _v0))) (@And
  (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2 _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@NormalFinalClosure.machine2 _v0)) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@NormalFinalClosure.machine2
  _v0) _v1 _v4 _v15 _v5)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@NormalFinalClosure.machine2 _v0))) (∀ (_v17 :
  (@Bool)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2 _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@NormalFinalClosure.machine2 _v0)) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@NormalFinalClosure.machine2
  _v0) _v1 _v4 _v15 _v5)) (@NormalFinalClosure.old2 _v0 (@_v11 _v17)))))))) (@Or (@And (@Eq.{(0 + 1)} (@Nat) _v13 _v12)
  (@And (@Exists.{(0 + 1)} (@Bool) (fun (_v15 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v8)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v8) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v8 _v1 _v4
  _v12 _v9)) (@_v11 _v15)))) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2 _v0)) _v1 _v4)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@NormalFinalClosure.machine2 _v0) _v1 _v4 _v13 _v5)
  (@NormalFinalClosure.config2 _v0 _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v8 _v1 _v4 _v12 _v9))))) (@Or (@And
  (@Eq.{(0 + 1)} (@Nat) _v13 _v12) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v8))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v8) _v1 _v4
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v8 _v1 _v4 _v12 _v9)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v8))
  (@And (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.encodedRelationLanguage
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0) _v1 _v2) (@Bool.false)) (@Eq.{(0 +
  1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2
  _v0)) _v1 _v4) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@NormalFinalClosure.machine2 _v0) _v1 _v4 _v13 _v5)
  (@NormalFinalClosure.config2 _v0 _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v8 _v1 _v4 _v12 _v9))))))
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
  _v1 _v19)) (@And (@Eq.{(0 + 1)} (@Nat) _v16 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v15 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Exists.{(0 + 1)} (@Nat) (fun (_v20
  : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v21 : (@Nat)) =>
(@And (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.tagMatches (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v15 _v16) (@Fin.append.{(0 + 1)} _v15 _v16 (@Bool) _v17 _v18))
  (@Bool.true)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Nat))
  (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros? (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v15 _v16) (@Fin.append.{(0 + 1)} _v15 _v16 (@Bool) _v17 _v18)) (@Option.some.{0}
  (@Nat) _v21)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Nat) (@Nat)))
  (@Pnp4.Frontier.ContractExpansion.contentHeader? (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v15 _v16) (@Fin.append.{(0 + 1)} _v15 _v16 (@Bool) _v17 _v18)) (@Option.some.{0} (@Prod.{0, 0} (@Nat)
  (@Nat)) (@Prod.mk.{0, 0} (@Nat) (@Nat) _v20 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v21) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))) (let _v22 :
  (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v15 _v16);
(let _v23 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v1);
(let _v24 : (@Nat) := (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v22 (@Min.min.{0}
  (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v21)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v20)) _v22));
(let _v25 : (@Nat) := (@Cursor.Target.W _v0 _v20);
(@And (@LT.lt.{0} (@Nat) (@instLTNat) (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v21))
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v20)) _v22) _v22) (@And (@LE.le.{0}
  (@Nat) (@instLENat) (@Pnp4.Frontier.ContractExpansion.bitLength _v20) _v24) (@And (@LE.le.{0} (@Nat) (@instLENat) _v25
  _v24) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v8))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v8) _v1 _v4
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v8 _v1 _v4 _v12 _v9)) _v10) (@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v22 _v21)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v20) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)) (fun (_v26 : (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v22 _v21)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v20) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4))) =>
(@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v8) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v8 _v1 _v4
  _v12 _v9)) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v22 _v21) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))
  _v20) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v26)) (@Exists.{(0 + 1)} (@Bool) (fun (_v27 :
  (@Bool)) =>
(@And (@Eq.{(0 + 1)} (@Bool) _v27 (@Pnp3.Complexity.Uniform.V1.encodedRelationLanguage
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0) _v1 _v2)) (@And (@Eq.{(0 + 1)}
  (@Bool) _v27 (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v15 _v16 _v17 _v18))
  (@And (@Iff (@Eq.{(0 + 1)} (@Bool) _v27 (@Bool.true)) (@Exists.{(0 + 1)} (@Nat) (fun (_v28 : (@Nat)) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@Pnp4.Frontier.ContractExpansion.readNatBE (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v21)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v20))
  (@Pnp4.Frontier.ContractExpansion.bitLength _v25)) _v25) (@Pnp4.Frontier.ContractExpansion.padWord (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v15 _v16) (@Fin.append.{(0 + 1)} _v15 _v16 (@Bool) _v17 _v18)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat)
  (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v21)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v20)) (@Pnp4.Frontier.ContractExpansion.bitLength _v25)) _v25)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v21))
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v20))
  (@Pnp4.Frontier.ContractExpansion.bitLength _v25)) (@Option.some.{0} (@Nat) _v28)) (@And (@LE.le.{0} (@Nat) (@instLENat)
  _v28 _v25) (@And (∀ (_v29 : (@Nat)),
(∀ (_v30 : (@LT.lt.{0} (@Nat) (@instLTNat) _v29 _v28)),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v15 _v16) (@Fin.append.{(0 + 1)} _v15 _v16 (@Bool) _v17 _v18) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 :
  Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))) _v21)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v20))
  (@Pnp4.Frontier.ContractExpansion.bitLength _v25)) _v29)) (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v15 _v16) (@Fin.append.{(0 + 1)} _v15 _v16 (@Bool) _v17
  _v18) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v21)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v20))
  (@Pnp4.Frontier.ContractExpansion.bitLength _v25)) _v25) _v29))))) (∀ (_v29 : (@Nat)),
(∀ (_v30 : (@LE.le.{0} (@Nat) (@instLENat) _v28 _v29)),
(∀ (_v31 : (@LT.lt.{0} (@Nat) (@instLTNat) _v29 _v25)),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v15 _v16) (@Fin.append.{(0 + 1)} _v15 _v16 (@Bool) _v17 _v18) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 :
  Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))) _v21)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v20))
  (@Pnp4.Frontier.ContractExpansion.bitLength _v25)) _v29)) (@Bool.false))))))))))) (@Eq.{(0 + 1)}
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2
  _v0)) _v1 _v4) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@NormalFinalClosure.machine2 _v0) _v1 _v4 _v13 _v5)
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2
  _v0)) _v1 _v4 (@ite.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2
  _v0))) (@Eq.{(0 + 1)} (@Bool) _v27 (@Bool.true)) (@instDecidableEqBool _v27 (@Bool.true))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@NormalFinalClosure.machine2 _v0))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@NormalFinalClosure.machine2 _v0))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v22 _v21) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v20) (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v26) (@NormalFinalClosure.Target.cleared _v1 _v4
  (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v8) _v1 _v4
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v8 _v1 _v4 _v12 _v9)) _v23 _v24
  _v20))))))))))))))))))))))))))))))))))))))))))))))) (@And (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v13)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) _v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4503599627370496 : Nat) (@instOfNatNat
  (4503599627370496 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 :
  Nat))))) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (4503599627370496 : Nat) (@instOfNatNat (4503599627370496 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))
  (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool)))
  (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))))) (@StandardTMBridgeClosure.steps _v3 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v13)) _v6) (@Option.some.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool)))) _v14)) (@And (@And (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))) _v14) (@Option.some.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@Prod.mk.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4 _v13 _v5)) (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))
  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (0 : Nat)))))) (∀ (_v15 : (@Int)),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Turing.Tape.nth.{0} (@Prod.{0, 0} (@Bool) (@Option.{0}
  (@Bool))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))) (@Turing.TM0.Cfg.Tape.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))) _v14) _v15) (@dite.{(0 + 1)} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@And (@LE.le.{0} (@Int)
  (@Int.instLEInt) (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int)
  (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v13 _v5)))) _v15)) (@LT.lt.{0} (@Int) (@Int.instLTInt) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int)
  (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4 _v13 _v5)))) _v15) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)))) (@instDecidableAnd (@LE.le.{0} (@Int) (@Int.instLEInt)
  (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0}
  (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1
  _v4) (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4 _v13 _v5)))) _v15)) (@LT.lt.{0} (@Int) (@Int.instLTInt)
  (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v13 _v5)))) _v15) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)))
  (@Int.decLe (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int)
  (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v13 _v5)))) _v15)) (@Int.decLt (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd))
  (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4 _v13 _v5)))) _v15) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)))) (fun (_v16 : (@And (@LE.le.{0} (@Int) (@Int.instLEInt)
  (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0}
  (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1
  _v4) (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4 _v13 _v5)))) _v15)) (@LT.lt.{0} (@Int) (@Int.instLTInt)
  (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v13 _v5)))) _v15) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4))))) =>
(@Prod.mk.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@Decidable.decide (@Eq.{(0 + 1)} (@Int) (@HAdd.hAdd.{0, 0, 0} (@Int)
  (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v13 _v5)))) _v15) (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat)))) (@Int.instDecidableEq (@HAdd.hAdd.{0, 0,
  0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v13 _v5)))) _v15) (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))))) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v13 _v5) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Int.toNat (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int)
  (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v13 _v5)))) _v15)) (@Decidable.byContradiction (@LT.lt.{0} (@Nat) (@instLTNat) (@Int.toNat (@HAdd.hAdd.{0, 0, 0} (@Int)
  (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v13 _v5)))) _v15)) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)) (@Nat.decLt (@Int.toNat (@HAdd.hAdd.{0, 0, 0}
  (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v13 _v5)))) _v15)) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)) (fun (_v17 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat)
  (@Int.toNat (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int)
  (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v13 _v5)))) _v15)) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)))) =>
(@StandardTMBridgeClosure.raw_full._proof_1 _v0 _v1 _v2 _v13 _v15 _v16 _v17))))))) (fun (_v16 : (@Not (@And (@LE.le.{0}
  (@Int) (@Int.instLEInt) (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int)
  (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v13 _v5)))) _v15)) (@LT.lt.{0} (@Int) (@Int.instLTInt) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int)
  (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4 _v13 _v5)))) _v15) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)))))) =>
(@Prod.mk.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@Bool.false) (@Option.none.{0} (@Bool)))))))) (@And (∀ (_v15 : (@Nat)),
(∀ (_v16 : (@LE.le.{0} (@Nat) (@instLENat) _v15 _v13)),
(@Exists.{(0 + 1)} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool)))) (fun (_v17 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0}
  (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4
  : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))))) (@StandardTMBridgeClosure.steps _v3 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v15)) _v6) (@Option.some.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool)))) _v17)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))) _v17) (@Option.some.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@Prod.mk.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4 _v15 _v5)) (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))
  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (0 : Nat)))))) (∀ (_v18 : (@Int)),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Turing.Tape.nth.{0} (@Prod.{0, 0} (@Bool) (@Option.{0}
  (@Bool))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))) (@Turing.TM0.Cfg.Tape.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))) _v17) _v18) (@dite.{(0 + 1)} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@And (@LE.le.{0} (@Int)
  (@Int.instLEInt) (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int)
  (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v15 _v5)))) _v18)) (@LT.lt.{0} (@Int) (@Int.instLTInt) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int)
  (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4 _v15 _v5)))) _v18) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)))) (@instDecidableAnd (@LE.le.{0} (@Int) (@Int.instLEInt)
  (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0}
  (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1
  _v4) (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4 _v15 _v5)))) _v18)) (@LT.lt.{0} (@Int) (@Int.instLTInt)
  (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v15 _v5)))) _v18) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)))
  (@Int.decLe (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int)
  (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v15 _v5)))) _v18)) (@Int.decLt (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd))
  (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4 _v15 _v5)))) _v18) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)))) (fun (_v19 : (@And (@LE.le.{0} (@Int) (@Int.instLEInt)
  (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0}
  (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1
  _v4) (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4 _v15 _v5)))) _v18)) (@LT.lt.{0} (@Int) (@Int.instLTInt)
  (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v15 _v5)))) _v18) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4))))) =>
(@Prod.mk.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@Decidable.decide (@Eq.{(0 + 1)} (@Int) (@HAdd.hAdd.{0, 0, 0} (@Int)
  (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v15 _v5)))) _v18) (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat)))) (@Int.instDecidableEq (@HAdd.hAdd.{0, 0,
  0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v15 _v5)))) _v18) (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))))) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v15 _v5) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Int.toNat (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int)
  (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v15 _v5)))) _v18)) (@Decidable.byContradiction (@LT.lt.{0} (@Nat) (@instLTNat) (@Int.toNat (@HAdd.hAdd.{0, 0, 0} (@Int)
  (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v15 _v5)))) _v18)) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)) (@Nat.decLt (@Int.toNat (@HAdd.hAdd.{0, 0, 0}
  (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v15 _v5)))) _v18)) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)) (fun (_v20 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat)
  (@Int.toNat (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int)
  (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v15 _v5)))) _v18)) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)))) =>
(@StandardTMBridgeClosure.raw_full._proof_1 _v0 _v1 _v2 _v15 _v18 _v19 _v20))))))) (fun (_v19 : (@Not (@And (@LE.le.{0}
  (@Int) (@Int.instLEInt) (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int)
  (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4
  _v15 _v5)))) _v18)) (@LT.lt.{0} (@Int) (@Int.instLTInt) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int)
  (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3) _v1 _v4
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v3 _v1 _v4 _v15 _v5)))) _v18) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v4)))))) =>
(@Prod.mk.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@Bool.false) (@Option.none.{0} (@Bool))))))))))))) (@And (∀ (_v15 :
  (@Nat)),
(∀ (_v16 : (@LE.le.{0} (@Nat) (@instLENat) _v15 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v13)))),
(@Exists.{(0 + 1)} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool)))) (fun (_v17 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0}
  (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4
  : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0,
  0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat
  (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))) (@StandardTMBridgeClosure.steps _v3 _v15 _v6) (@Option.some.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0}
  (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3))
  (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool)))) _v17)))))) (@And (∀ (_v15 : (@Nat)),
(∀ (_v16 : (@LT.lt.{0} (@Nat) (@instLTNat) _v15 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v13)))),
(∀ (_v17 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))),
(∀ (_v18 : (@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))))) (@StandardTMBridgeClosure.steps _v3 _v15 _v6) (@Option.some.{0}
  (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool)))) _v17))),
(@And (@Ne.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool)
  (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) _v17) (@Option.some.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v3) (@OfNat.ofNat.{0} (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (0 :
  Nat)))))) (@And (@Ne.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3))
  (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool)
  (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) _v17) (@Option.some.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v3) (@OfNat.ofNat.{0} (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (0 :
  Nat)))))) (∀ (_v19 : (@Bool)),
(@Ne.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool)
  (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) _v17) (@Option.some.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))) (@_v7 _v19) (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))
  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (0 : Nat))))))))))))) (@Or
  (@Exists.{(0 + 1)} (@Bool) (fun (_v15 : (@Bool)) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool)
  (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) _v14) (@Option.some.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2 _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4
  : Nat) (@instOfNatNat (4 : Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@NormalFinalClosure.machine2 _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@_v7 _v15)
  (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (0 : Nat)))))) (@Ne.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool)
  (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))))) (@Turing.TM0.step.{0, 0} (@Prod.{0, 0} (@Bool)
  (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))) (@StandardTMBridgeClosure.compile _v3) _v14) (@Option.none.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool)
  (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))))))))) (@Exists.{(0 + 1)} (@Bool) (fun (_v15 : (@Bool))
  =>
(@And (@Eq.{(0 + 1)} (@Bool) _v15 (@Pnp3.Complexity.Uniform.V1.encodedRelationLanguage
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0) _v1 _v2)) (@And (@Eq.{(0 + 1)}
  (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool)))
  (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))) _v14) (@Option.some.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))) (@ite.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3))
  (@Eq.{(0 + 1)} (@Bool) _v15 (@Bool.true)) (@instDecidableEqBool _v15 (@Bool.true))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v3) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v3)) (@OfNat.ofNat.{0}
  (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))
  (0 : Nat)))))) (@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool)))
  (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))))) (@Turing.TM0.step.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))) (@StandardTMBridgeClosure.compile _v3) _v14) (@Option.none.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool)
  (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v3)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool)))))))))))))))))))))))))))))))))))) := by
  exact @StandardTMBridgeClosure.raw_full

-- Independent literal expected type for StandardTMBridgeClosure.simulation.
noncomputable def PartACanonical.Types.p0773 :
(∀ (_v0 : (@Pnp3.Complexity.Uniform.V1.UniformTM)),
(@StandardTMBridgeClosure.Target.Simulation _v0)) := by
  exact @StandardTMBridgeClosure.simulation

-- Complete literal proposition for StandardTMBridgeClosure.simulation; original proof reused.
theorem PartACanonical.Surface.m0464 :
(∀ (_v0 : (@Pnp3.Complexity.Uniform.V1.UniformTM)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(let _v5 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v0 _v1 _v2 _v4);
(let _v6 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool)))) := (@Turing.TM0.init.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) (@StandardTMBridgeClosure.encode (@List.ofFn.{0}
  (@Bool) _v1 _v4)));
(∀ (_v7 : (∀ (_v7 : (@Nat)),
(∀ (_v8 : (@LT.lt.{0} (@Nat) (@instLTNat) _v7 _v3)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2 _v7 _v5)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v0))
  (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2
  _v7 _v5)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v0)))))),
(∀ (_v8 : (∀ (_v8 : (@Nat)),
(∀ (_v9 : (@LT.lt.{0} (@Nat) (@instLTNat) _v8 _v3)),
(∀ (_v10 : (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Move) (@Prod.snd.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move) (@Prod.snd.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step _v0
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2 _v8 _v5)) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2
  _v8 _v5) (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2 _v8 _v5)))))) (@Pnp3.Complexity.Uniform.V1.Move.right))),
(@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2
  _v8 _v5))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1
  _v2)))))),
(@And (∀ (_v9 : (@Nat)),
(∀ (_v10 : (@LE.le.{0} (@Nat) (@instLENat) _v9 _v3)),
(@Exists.{(0 + 1)} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool)))) (fun (_v11 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0}
  (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4
  : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))))) (@StandardTMBridgeClosure.steps _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v9)) _v6) (@Option.some.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool)))) _v11)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))) _v11) (@Option.some.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@Prod.mk.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2 _v9 _v5)) (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))
  (@PartACanonical.PrivateABI.a0050) (0 : Nat)))))) (∀ (_v12 : (@Int)),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Turing.Tape.nth.{0} (@Prod.{0, 0} (@Bool) (@Option.{0}
  (@Bool))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))) (@Turing.TM0.Cfg.Tape.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))) _v11) _v12) (@dite.{(0 + 1)} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@And (@LE.le.{0} (@Int)
  (@Int.instLEInt) (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int)
  (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2
  _v9 _v5)))) _v12)) (@LT.lt.{0} (@Int) (@Int.instLTInt) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int)
  (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2 _v9 _v5)))) _v12) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)))) (@instDecidableAnd (@LE.le.{0} (@Int) (@Int.instLEInt)
  (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0}
  (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1
  _v2) (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2 _v9 _v5)))) _v12)) (@LT.lt.{0} (@Int) (@Int.instLTInt)
  (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2
  _v9 _v5)))) _v12) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))) (@Int.decLe
  (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0}
  (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1
  _v2) (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2 _v9 _v5)))) _v12)) (@Int.decLt (@HAdd.hAdd.{0, 0, 0} (@Int)
  (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2
  _v9 _v5)))) _v12) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)))) (fun (_v13
  : (@And (@LE.le.{0} (@Int) (@Int.instLEInt) (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0,
  0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2
  _v9 _v5)))) _v12)) (@LT.lt.{0} (@Int) (@Int.instLTInt) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int)
  (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2 _v9 _v5)))) _v12) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))))) =>
(@Prod.mk.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@Decidable.decide (@Eq.{(0 + 1)} (@Int) (@HAdd.hAdd.{0, 0, 0} (@Int)
  (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2
  _v9 _v5)))) _v12) (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat)))) (@Int.instDecidableEq (@HAdd.hAdd.{0, 0,
  0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2
  _v9 _v5)))) _v12) (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))))) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2
  _v9 _v5) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Int.toNat (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int)
  (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2
  _v9 _v5)))) _v12)) (@StandardTMBridgeClosure.Represents._proof_2 _v0 _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  _v0 _v1 _v2 _v9 _v5) _v12 _v13))))) (fun (_v13 : (@Not (@And (@LE.le.{0} (@Int) (@Int.instLEInt) (@OfNat.ofNat.{0}
  (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int)
  (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2 _v9 _v5)))) _v12)) (@LT.lt.{0} (@Int) (@Int.instLTInt)
  (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2
  _v9 _v5)))) _v12) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)))))) =>
(@Prod.mk.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@Bool.false) (@Option.none.{0} (@Bool))))))))))))) (∀ (_v9 : (@Nat)),
(∀ (_v10 : (@LT.lt.{0} (@Nat) (@instLTNat) _v9 _v3)),
(let _v11 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2) :=
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2 _v9 _v5);
(let _v12 : (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Prod.{0, 0} (@Option.{0}
  (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) := (@Pnp3.Complexity.Uniform.V1.UniformTM.step _v0
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v11)
  (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v11
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v11)));
(@Exists.{(0 + 1)} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool)))) (fun (_v13 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0}
  (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4
  : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))))) (@StandardTMBridgeClosure.steps _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v9)) _v6) (@Option.some.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool)))) _v13)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))) _v13) (@Option.some.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@Prod.mk.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))) (@Prod.fst.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Prod.{0, 0} (@Option.{0}
  (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) _v12) (@StandardTMBridgeClosure.Target.Simulation.match_1.{(0 + 1)} (fun
  (_v14 : (@Pnp3.Complexity.Uniform.V1.Move)) =>
(@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@Prod.snd.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move) (@Prod.snd.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) _v12)) (fun (_v14 : (@Unit)) =>
(@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (1 : Nat) (@Fin.instOfNat
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@StandardTMBridgeClosure.Target.Simulation._proof_1) (1 :
  Nat)))) (fun (_v14 : (@Unit)) =>
(@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (2 : Nat) (@Fin.instOfNat
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@StandardTMBridgeClosure.Target.Simulation._proof_1) (2 :
  Nat)))) (fun (_v14 : (@Unit)) =>
(@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (3 : Nat) (@Fin.instOfNat
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@StandardTMBridgeClosure.Target.Simulation._proof_1) (3 :
  Nat)))))))) (∀ (_v14 : (@Int)),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Turing.Tape.nth.{0} (@Prod.{0, 0} (@Bool) (@Option.{0}
  (@Bool))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))) (@Turing.TM0.Cfg.Tape.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))) _v13) _v14) (@ite.{(0 + 1)} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Eq.{(0 + 1)} (@Int) _v14
  (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat)))) (@Int.instDecidableEq _v14 (@OfNat.ofNat.{0} (@Int) (0 :
  Nat) (@instOfNat (0 : Nat)))) (@Prod.mk.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@Decidable.decide (@Eq.{(0 + 1)} (@Nat)
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v11)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat)))) (@instDecidableEqNat (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v11))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))) (@Prod.fst.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move) (@Prod.snd.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) _v12))) (@dite.{(0 + 1)} (@Prod.{0, 0} (@Bool)
  (@Option.{0} (@Bool))) (@And (@LE.le.{0} (@Int) (@Int.instLEInt) (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 :
  Nat))) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int)
  (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v11))) _v14)) (@LT.lt.{0} (@Int) (@Int.instLTInt)
  (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v11))) _v14) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)))) (@instDecidableAnd (@LE.le.{0} (@Int) (@Int.instLEInt)
  (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0}
  (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1
  _v2) (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v11)))
  _v14)) (@LT.lt.{0} (@Int) (@Int.instLTInt) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int)
  (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v11))) _v14)
  (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))) (@Int.decLe (@OfNat.ofNat.{0}
  (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int)
  (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v11))) _v14))
  (@Int.decLt (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int)
  (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v11))) _v14) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)))) (fun (_v15 : (@And (@LE.le.{0} (@Int) (@Int.instLEInt)
  (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0}
  (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1
  _v2) (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v11)))
  _v14)) (@LT.lt.{0} (@Int) (@Int.instLTInt) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int)
  (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v11))) _v14)
  (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))))) =>
(@Prod.mk.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@Decidable.decide (@Eq.{(0 + 1)} (@Int) (@HAdd.hAdd.{0, 0, 0} (@Int)
  (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v11))) _v14) (@OfNat.ofNat.{0} (@Int) (0 : Nat)
  (@instOfNat (0 : Nat)))) (@Int.instDecidableEq (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int)
  (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v11))) _v14)
  (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))))) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v11 (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1
  _v2) (@Int.toNat (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int)
  (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v11))) _v14))
  (@StandardTMBridgeClosure.Target.Simulation._proof_2 _v0 _v1 _v2 _v4 _v9 _v14 _v15))))) (fun (_v15 : (@Not (@And
  (@LE.le.{0} (@Int) (@Int.instLEInt) (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0}
  (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v11))) _v14)) (@LT.lt.{0} (@Int) (@Int.instLTInt)
  (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v11))) _v14) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)))))) =>
(@Prod.mk.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@Bool.false) (@Option.none.{0} (@Bool)))))))))))))))))))))))))) := by
  exact @StandardTMBridgeClosure.simulation

-- Independent literal expected type for StandardTMBridgeClosure.simulation_full.
noncomputable def PartACanonical.Types.p0774 :
(∀ (_v0 : (@Pnp3.Complexity.Uniform.V1.UniformTM)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(let _v5 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v0 _v1 _v2 _v4);
(let _v6 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool)))) := (@Turing.TM0.init.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) (@StandardTMBridgeClosure.encode (@List.ofFn.{0}
  (@Bool) _v1 _v4)));
(∀ (_v7 : (∀ (_v7 : (@Nat)),
(∀ (_v8 : (@LT.lt.{0} (@Nat) (@instLTNat) _v7 _v3)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2 _v7 _v5)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v0))
  (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2
  _v7 _v5)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v0)))))),
(∀ (_v8 : (∀ (_v8 : (@Nat)),
(∀ (_v9 : (@LT.lt.{0} (@Nat) (@instLTNat) _v8 _v3)),
(∀ (_v10 : (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Move) (@Prod.snd.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move) (@Prod.snd.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step _v0
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2 _v8 _v5)) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2
  _v8 _v5) (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2 _v8 _v5)))))) (@Pnp3.Complexity.Uniform.V1.Move.right))),
(@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2
  _v8 _v5))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1
  _v2)))))),
(@And (∀ (_v9 : (@Nat)),
(∀ (_v10 : (@LE.le.{0} (@Nat) (@instLENat) _v9 _v3)),
(@Exists.{(0 + 1)} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool)))) (fun (_v11 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0}
  (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4
  : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))))) (@StandardTMBridgeClosure.steps _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v9)) _v6) (@Option.some.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool)))) _v11)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))) _v11) (@Option.some.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@Prod.mk.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2 _v9 _v5)) (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))
  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (0 : Nat)))))) (∀ (_v12 : (@Int)),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Turing.Tape.nth.{0} (@Prod.{0, 0} (@Bool) (@Option.{0}
  (@Bool))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))) (@Turing.TM0.Cfg.Tape.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))) _v11) _v12) (@dite.{(0 + 1)} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@And (@LE.le.{0} (@Int)
  (@Int.instLEInt) (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int)
  (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2
  _v9 _v5)))) _v12)) (@LT.lt.{0} (@Int) (@Int.instLTInt) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int)
  (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2 _v9 _v5)))) _v12) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)))) (@instDecidableAnd (@LE.le.{0} (@Int) (@Int.instLEInt)
  (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0}
  (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1
  _v2) (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2 _v9 _v5)))) _v12)) (@LT.lt.{0} (@Int) (@Int.instLTInt)
  (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2
  _v9 _v5)))) _v12) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))) (@Int.decLe
  (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0}
  (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1
  _v2) (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2 _v9 _v5)))) _v12)) (@Int.decLt (@HAdd.hAdd.{0, 0, 0} (@Int)
  (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2
  _v9 _v5)))) _v12) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)))) (fun (_v13
  : (@And (@LE.le.{0} (@Int) (@Int.instLEInt) (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0,
  0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2
  _v9 _v5)))) _v12)) (@LT.lt.{0} (@Int) (@Int.instLTInt) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int)
  (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2 _v9 _v5)))) _v12) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))))) =>
(@Prod.mk.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@Decidable.decide (@Eq.{(0 + 1)} (@Int) (@HAdd.hAdd.{0, 0, 0} (@Int)
  (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2
  _v9 _v5)))) _v12) (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat)))) (@Int.instDecidableEq (@HAdd.hAdd.{0, 0,
  0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2
  _v9 _v5)))) _v12) (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))))) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2
  _v9 _v5) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Int.toNat (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int)
  (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2
  _v9 _v5)))) _v12)) (@Decidable.byContradiction (@LT.lt.{0} (@Nat) (@instLTNat) (@Int.toNat (@HAdd.hAdd.{0, 0, 0} (@Int)
  (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2
  _v9 _v5)))) _v12)) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (@Nat.decLt (@Int.toNat (@HAdd.hAdd.{0, 0, 0}
  (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2
  _v9 _v5)))) _v12)) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (fun (_v14 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat)
  (@Int.toNat (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int)
  (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2
  _v9 _v5)))) _v12)) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)))) =>
(@StandardTMBridgeClosure.simulation_full._proof_3 _v0 _v1 _v2 _v4 _v9 _v12 _v13 _v14))))))) (fun (_v13 : (@Not (@And
  (@LE.le.{0} (@Int) (@Int.instLEInt) (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0}
  (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2
  _v9 _v5)))) _v12)) (@LT.lt.{0} (@Int) (@Int.instLTInt) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int)
  (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2 _v9 _v5)))) _v12) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)))))) =>
(@Prod.mk.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@Bool.false) (@Option.none.{0} (@Bool))))))))))))) (∀ (_v9 : (@Nat)),
(∀ (_v10 : (@LT.lt.{0} (@Nat) (@instLTNat) _v9 _v3)),
(let _v11 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2) :=
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2 _v9 _v5);
(let _v12 : (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Prod.{0, 0} (@Option.{0}
  (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) := (@Pnp3.Complexity.Uniform.V1.UniformTM.step _v0
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v11)
  (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v11
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v11)));
(@Exists.{(0 + 1)} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool)))) (fun (_v13 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0}
  (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4
  : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))))) (@StandardTMBridgeClosure.steps _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v9)) _v6) (@Option.some.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool)))) _v13)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))) _v13) (@Option.some.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@Prod.mk.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))) (@Prod.fst.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Prod.{0, 0} (@Option.{0}
  (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) _v12) (@StandardTMBridgeClosure.simulation_full.match_1.{(0 + 1)} (fun
  (_v14 : (@Pnp3.Complexity.Uniform.V1.Move)) =>
(@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@Prod.snd.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move) (@Prod.snd.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) _v12)) (fun (_v14 : (@Unit)) =>
(@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (1 : Nat) (@Fin.instOfNat
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (1 : Nat)))) (fun (_v14 : (@Unit)) =>
(@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (2 : Nat) (@Fin.instOfNat
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (2 : Nat)))) (fun (_v14 : (@Unit)) =>
(@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (3 : Nat) (@Fin.instOfNat
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (3 : Nat)))))))) (∀ (_v14 : (@Int)),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Turing.Tape.nth.{0} (@Prod.{0, 0} (@Bool) (@Option.{0}
  (@Bool))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))) (@Turing.TM0.Cfg.Tape.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))) _v13) _v14) (@ite.{(0 + 1)} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Eq.{(0 + 1)} (@Int) _v14
  (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat)))) (@Int.instDecidableEq _v14 (@OfNat.ofNat.{0} (@Int) (0 :
  Nat) (@instOfNat (0 : Nat)))) (@Prod.mk.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@Decidable.decide (@Eq.{(0 + 1)} (@Nat)
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v11)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat)))) (@instDecidableEqNat (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v11))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))) (@Prod.fst.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move) (@Prod.snd.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) _v12))) (@dite.{(0 + 1)} (@Prod.{0, 0} (@Bool)
  (@Option.{0} (@Bool))) (@And (@LE.le.{0} (@Int) (@Int.instLEInt) (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 :
  Nat))) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int)
  (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v11))) _v14)) (@LT.lt.{0} (@Int) (@Int.instLTInt)
  (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v11))) _v14) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)))) (@instDecidableAnd (@LE.le.{0} (@Int) (@Int.instLEInt)
  (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0}
  (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1
  _v2) (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v11)))
  _v14)) (@LT.lt.{0} (@Int) (@Int.instLTInt) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int)
  (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v11))) _v14)
  (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))) (@Int.decLe (@OfNat.ofNat.{0}
  (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int)
  (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v11))) _v14))
  (@Int.decLt (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int)
  (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v11))) _v14) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)))) (fun (_v15 : (@And (@LE.le.{0} (@Int) (@Int.instLEInt)
  (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0}
  (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1
  _v2) (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v11)))
  _v14)) (@LT.lt.{0} (@Int) (@Int.instLTInt) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int)
  (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v11))) _v14)
  (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))))) =>
(@Prod.mk.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@Decidable.decide (@Eq.{(0 + 1)} (@Int) (@HAdd.hAdd.{0, 0, 0} (@Int)
  (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v11))) _v14) (@OfNat.ofNat.{0} (@Int) (0 : Nat)
  (@instOfNat (0 : Nat)))) (@Int.instDecidableEq (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int)
  (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v11))) _v14)
  (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))))) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v11 (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1
  _v2) (@Int.toNat (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int)
  (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v11))) _v14)) (@Decidable.byContradiction (@LT.lt.{0}
  (@Nat) (@instLTNat) (@Int.toNat (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd))
  (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v11))) _v14))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (@Nat.decLt (@Int.toNat (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int)
  (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v11))) _v14)) (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v1 _v2)) (fun (_v16 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat) (@Int.toNat (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int)
  (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v11))) _v14)) (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v1 _v2)))) =>
(@StandardTMBridgeClosure.simulation_full._proof_3 _v0 _v1 _v2 _v4 _v9 _v14 _v15 _v16))))))) (fun (_v15 : (@Not (@And
  (@LE.le.{0} (@Int) (@Int.instLEInt) (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0}
  (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v11))) _v14)) (@LT.lt.{0} (@Int) (@Int.instLTInt)
  (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v11))) _v14) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)))))) =>
(@Prod.mk.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@Bool.false) (@Option.none.{0} (@Bool)))))))))))))))))))))))))) := by
  exact @StandardTMBridgeClosure.simulation_full

-- Complete literal proposition for StandardTMBridgeClosure.simulation_full; original proof reused.
theorem PartACanonical.Surface.m0465 :
(∀ (_v0 : (@Pnp3.Complexity.Uniform.V1.UniformTM)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(let _v5 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v0 _v1 _v2 _v4);
(let _v6 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool)))) := (@Turing.TM0.init.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) (@StandardTMBridgeClosure.encode (@List.ofFn.{0}
  (@Bool) _v1 _v4)));
(∀ (_v7 : (∀ (_v7 : (@Nat)),
(∀ (_v8 : (@LT.lt.{0} (@Nat) (@instLTNat) _v7 _v3)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2 _v7 _v5)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v0))
  (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2
  _v7 _v5)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v0)))))),
(∀ (_v8 : (∀ (_v8 : (@Nat)),
(∀ (_v9 : (@LT.lt.{0} (@Nat) (@instLTNat) _v8 _v3)),
(∀ (_v10 : (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Move) (@Prod.snd.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move) (@Prod.snd.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step _v0
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2 _v8 _v5)) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2
  _v8 _v5) (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2 _v8 _v5)))))) (@Pnp3.Complexity.Uniform.V1.Move.right))),
(@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2
  _v8 _v5))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1
  _v2)))))),
(@And (∀ (_v9 : (@Nat)),
(∀ (_v10 : (@LE.le.{0} (@Nat) (@instLENat) _v9 _v3)),
(@Exists.{(0 + 1)} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool)))) (fun (_v11 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0}
  (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4
  : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))))) (@StandardTMBridgeClosure.steps _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v9)) _v6) (@Option.some.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool)))) _v11)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))) _v11) (@Option.some.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@Prod.mk.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2 _v9 _v5)) (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))
  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (0 : Nat)))))) (∀ (_v12 : (@Int)),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Turing.Tape.nth.{0} (@Prod.{0, 0} (@Bool) (@Option.{0}
  (@Bool))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))) (@Turing.TM0.Cfg.Tape.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))) _v11) _v12) (@dite.{(0 + 1)} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@And (@LE.le.{0} (@Int)
  (@Int.instLEInt) (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int)
  (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2
  _v9 _v5)))) _v12)) (@LT.lt.{0} (@Int) (@Int.instLTInt) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int)
  (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2 _v9 _v5)))) _v12) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)))) (@instDecidableAnd (@LE.le.{0} (@Int) (@Int.instLEInt)
  (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0}
  (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1
  _v2) (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2 _v9 _v5)))) _v12)) (@LT.lt.{0} (@Int) (@Int.instLTInt)
  (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2
  _v9 _v5)))) _v12) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))) (@Int.decLe
  (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0}
  (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1
  _v2) (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2 _v9 _v5)))) _v12)) (@Int.decLt (@HAdd.hAdd.{0, 0, 0} (@Int)
  (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2
  _v9 _v5)))) _v12) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)))) (fun (_v13
  : (@And (@LE.le.{0} (@Int) (@Int.instLEInt) (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0,
  0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2
  _v9 _v5)))) _v12)) (@LT.lt.{0} (@Int) (@Int.instLTInt) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int)
  (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2 _v9 _v5)))) _v12) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))))) =>
(@Prod.mk.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@Decidable.decide (@Eq.{(0 + 1)} (@Int) (@HAdd.hAdd.{0, 0, 0} (@Int)
  (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2
  _v9 _v5)))) _v12) (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat)))) (@Int.instDecidableEq (@HAdd.hAdd.{0, 0,
  0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2
  _v9 _v5)))) _v12) (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))))) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2
  _v9 _v5) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Int.toNat (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int)
  (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2
  _v9 _v5)))) _v12)) (@Decidable.byContradiction (@LT.lt.{0} (@Nat) (@instLTNat) (@Int.toNat (@HAdd.hAdd.{0, 0, 0} (@Int)
  (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2
  _v9 _v5)))) _v12)) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (@Nat.decLt (@Int.toNat (@HAdd.hAdd.{0, 0, 0}
  (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2
  _v9 _v5)))) _v12)) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (fun (_v14 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat)
  (@Int.toNat (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int)
  (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2
  _v9 _v5)))) _v12)) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)))) =>
(@StandardTMBridgeClosure.simulation_full._proof_3 _v0 _v1 _v2 _v4 _v9 _v12 _v13 _v14))))))) (fun (_v13 : (@Not (@And
  (@LE.le.{0} (@Int) (@Int.instLEInt) (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0}
  (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2
  _v9 _v5)))) _v12)) (@LT.lt.{0} (@Int) (@Int.instLTInt) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int)
  (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2 _v9 _v5)))) _v12) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)))))) =>
(@Prod.mk.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@Bool.false) (@Option.none.{0} (@Bool))))))))))))) (∀ (_v9 : (@Nat)),
(∀ (_v10 : (@LT.lt.{0} (@Nat) (@instLTNat) _v9 _v3)),
(let _v11 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2) :=
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v1 _v2 _v9 _v5);
(let _v12 : (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Prod.{0, 0} (@Option.{0}
  (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) := (@Pnp3.Complexity.Uniform.V1.UniformTM.step _v0
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v11)
  (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v11
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v11)));
(@Exists.{(0 + 1)} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool)))) (fun (_v13 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0}
  (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4
  : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))))) (@StandardTMBridgeClosure.steps _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v9)) _v6) (@Option.some.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool)))) _v13)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))) _v13) (@Option.some.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@Prod.mk.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))) (@Prod.fst.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Prod.{0, 0} (@Option.{0}
  (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) _v12) (@StandardTMBridgeClosure.simulation_full.match_1.{(0 + 1)} (fun
  (_v14 : (@Pnp3.Complexity.Uniform.V1.Move)) =>
(@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@Prod.snd.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move) (@Prod.snd.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) _v12)) (fun (_v14 : (@Unit)) =>
(@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (1 : Nat) (@Fin.instOfNat
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (1 : Nat)))) (fun (_v14 : (@Unit)) =>
(@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (2 : Nat) (@Fin.instOfNat
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (2 : Nat)))) (fun (_v14 : (@Unit)) =>
(@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (3 : Nat) (@Fin.instOfNat
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (3 : Nat)))))))) (∀ (_v14 : (@Int)),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Turing.Tape.nth.{0} (@Prod.{0, 0} (@Bool) (@Option.{0}
  (@Bool))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))) (@Turing.TM0.Cfg.Tape.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))) _v13) _v14) (@ite.{(0 + 1)} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Eq.{(0 + 1)} (@Int) _v14
  (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat)))) (@Int.instDecidableEq _v14 (@OfNat.ofNat.{0} (@Int) (0 :
  Nat) (@instOfNat (0 : Nat)))) (@Prod.mk.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@Decidable.decide (@Eq.{(0 + 1)} (@Nat)
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v11)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat)))) (@instDecidableEqNat (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v11))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))) (@Prod.fst.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move) (@Prod.snd.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) _v12))) (@dite.{(0 + 1)} (@Prod.{0, 0} (@Bool)
  (@Option.{0} (@Bool))) (@And (@LE.le.{0} (@Int) (@Int.instLEInt) (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 :
  Nat))) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int)
  (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v11))) _v14)) (@LT.lt.{0} (@Int) (@Int.instLTInt)
  (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v11))) _v14) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)))) (@instDecidableAnd (@LE.le.{0} (@Int) (@Int.instLEInt)
  (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0}
  (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1
  _v2) (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v11)))
  _v14)) (@LT.lt.{0} (@Int) (@Int.instLTInt) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int)
  (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v11))) _v14)
  (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))) (@Int.decLe (@OfNat.ofNat.{0}
  (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int)
  (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v11))) _v14))
  (@Int.decLt (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int)
  (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v11))) _v14) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)))) (fun (_v15 : (@And (@LE.le.{0} (@Int) (@Int.instLEInt)
  (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0}
  (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1
  _v2) (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v11)))
  _v14)) (@LT.lt.{0} (@Int) (@Int.instLTInt) (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int)
  (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v11))) _v14)
  (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))))) =>
(@Prod.mk.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@Decidable.decide (@Eq.{(0 + 1)} (@Int) (@HAdd.hAdd.{0, 0, 0} (@Int)
  (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v11))) _v14) (@OfNat.ofNat.{0} (@Int) (0 : Nat)
  (@instOfNat (0 : Nat)))) (@Int.instDecidableEq (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int)
  (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v11))) _v14)
  (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))))) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v11 (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1
  _v2) (@Int.toNat (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int)
  (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v11))) _v14)) (@Decidable.byContradiction (@LT.lt.{0}
  (@Nat) (@instLTNat) (@Int.toNat (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd))
  (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v11))) _v14))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (@Nat.decLt (@Int.toNat (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int)
  (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v11))) _v14)) (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v1 _v2)) (fun (_v16 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat) (@Int.toNat (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int)
  (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v11))) _v14)) (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v1 _v2)))) =>
(@StandardTMBridgeClosure.simulation_full._proof_3 _v0 _v1 _v2 _v4 _v9 _v14 _v15 _v16))))))) (fun (_v15 : (@Not (@And
  (@LE.le.{0} (@Int) (@Int.instLEInt) (@OfNat.ofNat.{0} (@Int) (0 : Nat) (@instOfNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0}
  (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v11))) _v14)) (@LT.lt.{0} (@Int) (@Int.instLTInt)
  (@HAdd.hAdd.{0, 0, 0} (@Int) (@Int) (@Int) (@instHAdd.{0} (@Int) (@Int.instAdd)) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2 _v11))) _v14) (@Nat.cast.{0} (@Int) (@instNatCastInt)
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)))))) =>
(@Prod.mk.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@Bool.false) (@Option.none.{0} (@Bool)))))))))))))))))))))))))) := by
  exact @StandardTMBridgeClosure.simulation_full

-- Independent literal expected type for StandardTMBridgeClosure.steps.
noncomputable def PartACanonical.Types.p0775 :
(∀ (_v0 : (@Pnp3.Complexity.Uniform.V1.UniformTM)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))),
(@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool)))))))) := by
  exact @StandardTMBridgeClosure.steps

-- Independent literal expected type for StandardTMBridgeClosure.steps.eq_1.
noncomputable def PartACanonical.Types.p0776 :
(∀ (_v0 : (@Pnp3.Complexity.Uniform.V1.UniformTM)),
(∀ (_v1 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0,
  0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat
  (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))) (@StandardTMBridgeClosure.steps _v0 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v1)
  (@Option.some.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool)))) _v1)))) := by
  exact @StandardTMBridgeClosure.steps.eq_1

-- Complete literal proposition for StandardTMBridgeClosure.steps.eq_1; original proof reused.
theorem PartACanonical.Surface.m0466 :
(∀ (_v0 : (@Pnp3.Complexity.Uniform.V1.UniformTM)),
(∀ (_v1 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0,
  0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat
  (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))) (@StandardTMBridgeClosure.steps _v0 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v1)
  (@Option.some.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool)))) _v1)))) := by
  exact @StandardTMBridgeClosure.steps.eq_1

-- Independent literal expected type for StandardTMBridgeClosure.steps.eq_2.
noncomputable def PartACanonical.Types.p0777 :
(∀ (_v0 : (@Pnp3.Complexity.Uniform.V1.UniformTM)),
(∀ (_v1 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))),
(∀ (_v2 : (@Nat)),
(@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0,
  0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat
  (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))) (@StandardTMBridgeClosure.steps _v0 (@Nat.succ _v2) _v1) (@Option.bind.{0, 0} (@Turing.TM0.Cfg.{0, 0}
  (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool)))) (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool)))) (@Turing.TM0.step.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) (@StandardTMBridgeClosure.compile _v0) _v1)
  (@StandardTMBridgeClosure.steps _v0 _v2)))))) := by
  exact @StandardTMBridgeClosure.steps.eq_2

-- Complete literal proposition for StandardTMBridgeClosure.steps.eq_2; original proof reused.
theorem PartACanonical.Surface.m0467 :
(∀ (_v0 : (@Pnp3.Complexity.Uniform.V1.UniformTM)),
(∀ (_v1 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))),
(∀ (_v2 : (@Nat)),
(@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0,
  0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat
  (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))) (@StandardTMBridgeClosure.steps _v0 (@Nat.succ _v2) _v1) (@Option.bind.{0, 0} (@Turing.TM0.Cfg.{0, 0}
  (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool)))) (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool)))) (@Turing.TM0.step.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) (@StandardTMBridgeClosure.compile _v0) _v1)
  (@StandardTMBridgeClosure.steps _v0 _v2)))))) := by
  exact @StandardTMBridgeClosure.steps.eq_2

-- Independent literal expected type for StandardTMBridgeClosure.steps_reaches.
noncomputable def PartACanonical.Types.p0778 :
(∀ (_v0 : (@Pnp3.Complexity.Uniform.V1.UniformTM)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))),
(∀ (_v3 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))),
(∀ (_v4 : (@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))))) (@StandardTMBridgeClosure.steps _v0 _v1 _v2) (@Option.some.{0}
  (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool)))) _v3))),
(@Turing.TM0.Reaches.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) (@StandardTMBridgeClosure.compile _v0) _v2 _v3)))))) := by
  exact @StandardTMBridgeClosure.steps_reaches

-- Complete literal proposition for StandardTMBridgeClosure.steps_reaches; original proof reused.
theorem PartACanonical.Surface.m0468 :
(∀ (_v0 : (@Pnp3.Complexity.Uniform.V1.UniformTM)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))),
(∀ (_v3 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))),
(∀ (_v4 : (@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))))) (@StandardTMBridgeClosure.steps _v0 _v1 _v2) (@Option.some.{0}
  (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool)))) _v3))),
(@Turing.TM0.Reaches.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) (@StandardTMBridgeClosure.compile _v0) _v2 _v3)))))) := by
  exact @StandardTMBridgeClosure.steps_reaches

-- Independent literal expected type for StandardTMBridgeClosure.steps_reaches_full.
noncomputable def PartACanonical.Types.p0779 :
(∀ (_v0 : (@Pnp3.Complexity.Uniform.V1.UniformTM)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))),
(∀ (_v3 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))),
(∀ (_v4 : (@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))))) (@StandardTMBridgeClosure.steps _v0 _v1 _v2) (@Option.some.{0}
  (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool)))) _v3))),
(@Relation.ReflTransGen.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0,
  0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat
  (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool)))) (fun (_v5 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0}
  (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4
  : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))) =>
(fun (_v6 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))) =>
(@Membership.mem.{0, 0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0}
  (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4
  : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool)))) (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0}
  (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4
  : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))) (@Option.instMembership.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool)))
  (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))))) (@Turing.TM0.step.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))) (@StandardTMBridgeClosure.compile _v0) _v5) _v6))) _v2 _v3)))))) := by
  exact @StandardTMBridgeClosure.steps_reaches_full

-- Complete literal proposition for StandardTMBridgeClosure.steps_reaches_full; original proof reused.
theorem PartACanonical.Surface.m0469 :
(∀ (_v0 : (@Pnp3.Complexity.Uniform.V1.UniformTM)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))),
(∀ (_v3 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))),
(∀ (_v4 : (@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))))) (@StandardTMBridgeClosure.steps _v0 _v1 _v2) (@Option.some.{0}
  (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool)))) _v3))),
(@Relation.ReflTransGen.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0,
  0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat
  (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool)))) (fun (_v5 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0}
  (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4
  : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))) =>
(fun (_v6 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))) =>
(@Membership.mem.{0, 0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0}
  (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4
  : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool)))) (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0}
  (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4
  : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))) (@Option.instMembership.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool)))
  (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))))) (@Turing.TM0.step.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))) (@StandardTMBridgeClosure.compile _v0) _v5) _v6))) _v2 _v3)))))) := by
  exact @StandardTMBridgeClosure.steps_reaches_full

-- Independent literal expected type for Stream.Audit.check_accepted_budget.
noncomputable def PartACanonical.Types.p0780 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ {_v3 : (@Nat)},
(∀ (_v4 : (@Eq.{(0 + 1)} (@Nat) _v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v5 : (@LE.le.{0} (@Nat) (@instLENat) _v2 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 _v1))),
(∀ (_v6 : (@LE.le.{0} (@Nat) (@instLENat) _v3 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 _v1))),
(@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1)
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v0 _v1) _v2) _v3) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))))
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))))))))) := by
  exact @Stream.Audit.check_accepted_budget

-- Complete literal proposition for Stream.Audit.check_accepted_budget; original proof reused.
theorem PartACanonical.Surface.m0470 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ {_v3 : (@Nat)},
(∀ (_v4 : (@Eq.{(0 + 1)} (@Nat) _v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v5 : (@LE.le.{0} (@Nat) (@instLENat) _v2 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 _v1))),
(∀ (_v6 : (@LE.le.{0} (@Nat) (@instLENat) _v3 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 _v1))),
(@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1)
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v0 _v1) _v2) _v3) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))))
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))))))))) := by
  exact @Stream.Audit.check_accepted_budget

-- Independent literal expected type for Stream.Audit.check_accepted_rows_fit.
noncomputable def PartACanonical.Types.p0781 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ {_v3 : (@Nat)},
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v5 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v2)),
(∀ (_v6 : (@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v1
  _v2 _v4 _v5) (@Bool.true))),
(∀ {_v7 : (@AcceptedBody.Parsed _v0)},
(∀ (_v8 : (@Eq.{(0 + 1)} (@Option.{0} (@Sigma.{0, 0} (@Nat) (fun (_v8 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v8))))) (@Pnp4.Frontier.ContractExpansion.contentInput?
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v4 _v5)) (@Option.some.{0} (@AcceptedBody.Parsed _v0)
  _v7))),
(∀ (_v9 : (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros?
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2
  (@Bool) _v4 _v5)) (@Option.some.{0} (@Nat) _v3))),
(@LE.le.{0} (@Nat) (@instLENat) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v10))) _v7)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v10 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v10))) _v7))) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHSub.{0} (@Nat) (@instSubNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat))
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v3)
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v10))) _v7)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v10 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v10))) _v7))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat
  (3 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))))))))))) := by
  exact @Stream.Audit.check_accepted_rows_fit

-- Complete literal proposition for Stream.Audit.check_accepted_rows_fit; original proof reused.
theorem PartACanonical.Surface.m0471 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ {_v3 : (@Nat)},
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v5 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v2)),
(∀ (_v6 : (@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v1
  _v2 _v4 _v5) (@Bool.true))),
(∀ {_v7 : (@AcceptedBody.Parsed _v0)},
(∀ (_v8 : (@Eq.{(0 + 1)} (@Option.{0} (@Sigma.{0, 0} (@Nat) (fun (_v8 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v8))))) (@Pnp4.Frontier.ContractExpansion.contentInput?
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v4 _v5)) (@Option.some.{0} (@AcceptedBody.Parsed _v0)
  _v7))),
(∀ (_v9 : (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros?
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2
  (@Bool) _v4 _v5)) (@Option.some.{0} (@Nat) _v3))),
(@LE.le.{0} (@Nat) (@instLENat) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v10))) _v7)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v10 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v10))) _v7))) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHSub.{0} (@Nat) (@instSubNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat))
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v3)
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v10))) _v7)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v10 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v10))) _v7))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat
  (3 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))))))))))) := by
  exact @Stream.Audit.check_accepted_rows_fit

-- Independent literal expected type for Stream.Audit.check_kernel.
noncomputable def PartACanonical.Types.p0782 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (∀ (_v7 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v8 : (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v5)),
(∀ (_v9 : (@LE.le.{0} (@Nat) (@instLENat) _v5 _v2)),
(∀ (_v10 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v3) _v4) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) _v6)),
(∀ (_v11 : (@LT.lt.{0} (@Nat) (@instLTNat) _v6 (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))),
(∀ (_v12 : (∀ (_v12 : (@Nat)),
(∀ (_v13 : (@LE.le.{0} (@Nat) (@instLENat) _v5 _v12)),
(∀ (_v14 : (@LT.lt.{0} (@Nat) (@instLTNat) _v12 _v2)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v15 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v7 _v12) (@Option.some.{0} (@Bool) _v15)))))))),
(∀ (_v13 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v7 _v2) (@Option.none.{0} (@Bool)))),
(∀ (_v14 : (∀ (_v14 : (@Nat)),
(∀ (_v15 : (@LT.lt.{0} (@Nat) (@instLTNat) _v2 _v14)),
(∀ (_v16 : (@LT.lt.{0} (@Nat) (@instLTNat) _v14 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v3)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v7 _v14) (@Option.some.{0} (@Bool) (@Bool.false))))))),
(∀ (_v15 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v7 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v3)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))) (@Option.none.{0} (@Bool)))),
(∀ (_v16 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v7 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v3) _v4) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))))) (@Option.none.{0} (@Bool)))),
(∀ (_v17 : (∀ (_v17 : (@Nat)),
(∀ (_v18 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v3) _v4) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) _v17)),
(∀ (_v19 : (@LT.lt.{0} (@Nat) (@instLTNat) _v17 _v6)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v7 _v17) (@Option.none.{0} (@Bool))))))),
(∀ (_v18 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v7 _v6) (@Option.some.{0} (@Bool) (@Bool.false)))),
(let _v19 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v2 _v3) _v4) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))));
(let _v20 : (@Nat) := (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HSub.hSub.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v6 _v19) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat))));
(let _v21 : (@Nat) := (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v4) _v20);
(∀ (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat) _v19 (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))),
(let _v23 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Stream.machine)) _v0
  _v1) := (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Stream.machine)) _v0
  _v1 (@Stream.unpaid (@Stream.Target.mode _v7 _v5 _v2)) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v19
  _v22) (fun (_v23 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))) =>
(@Stream.Target.image _v7 _v2 _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Bool.true) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v23))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v24 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v24 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))) (@And (∀ (_v25 : (@Nat)),
(∀ (_v26 : (@LT.lt.{0} (@Nat) (@instLTNat) _v25 _v21)),
(@Exists.{(0 + 1)} (@Nat) (fun (_v27 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v27 _v24) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Stream.machine)) _v0 _v1) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@Stream.machine) _v0 _v1 _v27 _v23) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Stream.machine)) _v0 _v1 (@Stream.paid (@Stream.Target.mode _v7
  (@Stream.Target.cursor _v5 _v2 _v25) _v2)) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v19 _v22) (fun
  (_v28 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))) =>
(@Stream.Target.image _v7 _v2 _v3 _v4 _v5 _v25 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v25 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Bool.true) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v28)))))))))) (@ite.{(0 + 1)} (Sort 0) (@LE.le.{0} (@Nat) (@instLENat)
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4) _v20) (@Nat.decLe (@HPow.hPow.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid)))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4) _v20) (@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat)
  (@Stream.Target.cursor _v5 _v2 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (fun (_v25 : (@LT.lt.{0} (@Nat) (@instLTNat) (@Stream.Target.cursor
  _v5 _v2 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))) =>
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Stream.machine))
  _v0 _v1) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Stream.machine) _v0 _v1 _v24 _v23)
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Stream.machine)) _v0 _v1
  (@Stream.q (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Stream.Target.cursor _v5 _v2 (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)) _v2) (@instDecidableEqNat (@Stream.Target.cursor _v5 _v2 (@HPow.hPow.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid)))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (57 : Nat)
  (@instOfNatNat (57 : Nat))) (@OfNat.ofNat.{0} (@Nat) (58 : Nat) (@instOfNatNat (58 : Nat))))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) (@Stream.Target.cursor _v5 _v2 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))) _v4)) _v25) (fun (_v26 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))) =>
(@Stream.Target.image _v7 _v2 _v3 _v4 _v5 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4) (@Bool.false) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v26))))))) (@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) _v6
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (fun (_v25 : (@LT.lt.{0} (@Nat) (@instLTNat) _v6
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))) =>
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Stream.machine))
  _v0 _v1) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Stream.machine) _v0 _v1 _v24 _v23)
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Stream.machine)) _v0 _v1
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@Stream.machine)) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v0
  _v1) _v6 _v25) (fun (_v26 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))) =>
(@Stream.Target.image _v7 _v2 _v3 _v4 _v5 _v20 _v20 (@Bool.true) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0
  _v1) _v26)))))))))))))))))))))))))))))))))))) := by
  exact @Stream.Audit.check_kernel

-- Complete literal proposition for Stream.Audit.check_kernel; original proof reused.
theorem PartACanonical.Surface.m0472 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (∀ (_v7 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v8 : (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v5)),
(∀ (_v9 : (@LE.le.{0} (@Nat) (@instLENat) _v5 _v2)),
(∀ (_v10 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v3) _v4) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) _v6)),
(∀ (_v11 : (@LT.lt.{0} (@Nat) (@instLTNat) _v6 (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))),
(∀ (_v12 : (∀ (_v12 : (@Nat)),
(∀ (_v13 : (@LE.le.{0} (@Nat) (@instLENat) _v5 _v12)),
(∀ (_v14 : (@LT.lt.{0} (@Nat) (@instLTNat) _v12 _v2)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v15 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v7 _v12) (@Option.some.{0} (@Bool) _v15)))))))),
(∀ (_v13 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v7 _v2) (@Option.none.{0} (@Bool)))),
(∀ (_v14 : (∀ (_v14 : (@Nat)),
(∀ (_v15 : (@LT.lt.{0} (@Nat) (@instLTNat) _v2 _v14)),
(∀ (_v16 : (@LT.lt.{0} (@Nat) (@instLTNat) _v14 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v3)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v7 _v14) (@Option.some.{0} (@Bool) (@Bool.false))))))),
(∀ (_v15 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v7 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v3)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))) (@Option.none.{0} (@Bool)))),
(∀ (_v16 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v7 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v3) _v4) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))))) (@Option.none.{0} (@Bool)))),
(∀ (_v17 : (∀ (_v17 : (@Nat)),
(∀ (_v18 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v3) _v4) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) _v17)),
(∀ (_v19 : (@LT.lt.{0} (@Nat) (@instLTNat) _v17 _v6)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v7 _v17) (@Option.none.{0} (@Bool))))))),
(∀ (_v18 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v7 _v6) (@Option.some.{0} (@Bool) (@Bool.false)))),
(let _v19 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v2 _v3) _v4) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))));
(let _v20 : (@Nat) := (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HSub.hSub.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v6 _v19) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat))));
(let _v21 : (@Nat) := (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v4) _v20);
(∀ (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat) _v19 (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))),
(let _v23 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Stream.machine)) _v0
  _v1) := (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Stream.machine)) _v0
  _v1 (@Stream.unpaid (@Stream.Target.mode _v7 _v5 _v2)) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v19
  _v22) (fun (_v23 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))) =>
(@Stream.Target.image _v7 _v2 _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Bool.true) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v23))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v24 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v24 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))) (@And (∀ (_v25 : (@Nat)),
(∀ (_v26 : (@LT.lt.{0} (@Nat) (@instLTNat) _v25 _v21)),
(@Exists.{(0 + 1)} (@Nat) (fun (_v27 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v27 _v24) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Stream.machine)) _v0 _v1) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@Stream.machine) _v0 _v1 _v27 _v23) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Stream.machine)) _v0 _v1 (@Stream.paid (@Stream.Target.mode _v7
  (@Stream.Target.cursor _v5 _v2 _v25) _v2)) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v19 _v22) (fun
  (_v28 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))) =>
(@Stream.Target.image _v7 _v2 _v3 _v4 _v5 _v25 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v25 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Bool.true) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v28)))))))))) (@ite.{(0 + 1)} (Sort 0) (@LE.le.{0} (@Nat) (@instLENat)
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4) _v20) (@Nat.decLe (@HPow.hPow.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid)))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4) _v20) (@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat)
  (@Stream.Target.cursor _v5 _v2 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (fun (_v25 : (@LT.lt.{0} (@Nat) (@instLTNat) (@Stream.Target.cursor
  _v5 _v2 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))) =>
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Stream.machine))
  _v0 _v1) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Stream.machine) _v0 _v1 _v24 _v23)
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Stream.machine)) _v0 _v1
  (@Stream.q (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Stream.Target.cursor _v5 _v2 (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)) _v2) (@instDecidableEqNat (@Stream.Target.cursor _v5 _v2 (@HPow.hPow.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid)))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (57 : Nat)
  (@instOfNatNat (57 : Nat))) (@OfNat.ofNat.{0} (@Nat) (58 : Nat) (@instOfNatNat (58 : Nat))))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) (@Stream.Target.cursor _v5 _v2 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))) _v4)) _v25) (fun (_v26 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))) =>
(@Stream.Target.image _v7 _v2 _v3 _v4 _v5 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4) (@Bool.false) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v26))))))) (@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) _v6
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (fun (_v25 : (@LT.lt.{0} (@Nat) (@instLTNat) _v6
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))) =>
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Stream.machine))
  _v0 _v1) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Stream.machine) _v0 _v1 _v24 _v23)
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Stream.machine)) _v0 _v1
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@Stream.machine)) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v0
  _v1) _v6 _v25) (fun (_v26 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))) =>
(@Stream.Target.image _v7 _v2 _v3 _v4 _v5 _v20 _v20 (@Bool.true) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0
  _v1) _v26)))))))))))))))))))))))))))))))))))) := by
  exact @Stream.Audit.check_kernel

-- Independent literal expected type for Stream.Audit.check_raw_accepted.
noncomputable def PartACanonical.Types.p0783 :
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v7)))) _v6)) (@And (@LE.le.{0} (@Nat) (@instLENat)
  (@Pnp3.Models.Partial.tableLen (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
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
  exact @Stream.Audit.check_raw_accepted

-- Complete literal proposition for Stream.Audit.check_raw_accepted; original proof reused.
theorem PartACanonical.Surface.m0473 :
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v7)))) _v6)) (@And (@LE.le.{0} (@Nat) (@instLENat)
  (@Pnp3.Models.Partial.tableLen (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
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
  exact @Stream.Audit.check_raw_accepted

-- Independent literal expected type for Stream.Audit.check_raw_body.
noncomputable def PartACanonical.Types.p0784 :
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
  exact @Stream.Audit.check_raw_body

-- Complete literal proposition for Stream.Audit.check_raw_body; original proof reused.
theorem PartACanonical.Surface.m0474 :
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
  exact @Stream.Audit.check_raw_body

-- Independent literal expected type for Stream.Audit.check_raw_budget_cells.
noncomputable def PartACanonical.Types.p0785 :
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
  exact @Stream.Audit.check_raw_budget_cells

-- Complete literal proposition for Stream.Audit.check_raw_budget_cells; original proof reused.
theorem PartACanonical.Surface.m0475 :
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
  exact @Stream.Audit.check_raw_budget_cells

-- Independent literal expected type for Stream.Audit.pin_BodyTarget_Orbit.
noncomputable def PartACanonical.Types.p0786 :
(∀ (_v0 : (@Nat)),
(Sort 0)) := by
  exact @Stream.Audit.pin_BodyTarget_Orbit

-- Independent literal expected type for Stream.Audit.pin_RawTarget_AcceptedOrbit.
noncomputable def PartACanonical.Types.p0787 :
(∀ (_v0 : (@Nat)),
(Sort 0)) := by
  exact @Stream.Audit.pin_RawTarget_AcceptedOrbit

-- Independent literal expected type for Stream.Audit.pin_Target_Kernel.
noncomputable def PartACanonical.Types.p0788 :
(Sort 0) := by
  exact @Stream.Audit.pin_Target_Kernel

-- Independent literal expected type for Stream.Audit.pin_Target_PartA.
noncomputable def PartACanonical.Types.p0789 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Pnp3.Complexity.Uniform.V1.UniformTM))),
(∀ (_v1 : (∀ (_v1 : (@Nat)),
(@Nat))),
(Sort 0))) := by
  exact @Stream.Audit.pin_Target_PartA

-- Independent literal expected type for Stream.Audit.pin_Target_cursor.
noncomputable def PartACanonical.Types.p0790 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(@Nat)))) := by
  exact @Stream.Audit.pin_Target_cursor

-- Independent literal expected type for Stream.Audit.pin_Target_image.
noncomputable def PartACanonical.Types.p0791 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Bool)),
(∀ (_v8 : (@Nat)),
(@Option.{0} (@Bool))))))))))) := by
  exact @Stream.Audit.pin_Target_image

-- Independent literal expected type for Stream.Audit.pin_Target_mode.
noncomputable def PartACanonical.Types.p0792 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))))) := by
  exact @Stream.Audit.pin_Target_mode

-- Independent literal expected type for Stream.Audit.pin_machine.
noncomputable def PartACanonical.Types.p0793 :
(@Pnp3.Complexity.Uniform.V1.UniformTM) := by
  exact @Stream.Audit.pin_machine

-- Independent literal expected type for Stream.Audit.pin_paid.
noncomputable def PartACanonical.Types.p0794 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))))) := by
  exact @Stream.Audit.pin_paid

-- Independent literal expected type for Stream.Audit.pin_q.
noncomputable def PartACanonical.Types.p0795 :
(∀ (_v0 : (@Nat)),
(@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))))) := by
  exact @Stream.Audit.pin_q

-- Independent literal expected type for Stream.Audit.pin_rawMachine.
noncomputable def PartACanonical.Types.p0796 :
(@Pnp3.Complexity.Uniform.V1.UniformTM) := by
  exact @Stream.Audit.pin_rawMachine

-- Independent literal expected type for Stream.Audit.pin_rows.
noncomputable def PartACanonical.Types.p0797 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))))),
(∀ (_v1 : (@Option.{0} (@Bool))),
(@Prod.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))))) := by
  exact @Stream.Audit.pin_rows

-- Independent literal expected type for Stream.Audit.pin_unpaid.
noncomputable def PartACanonical.Types.p0798 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))))) := by
  exact @Stream.Audit.pin_unpaid

-- Independent literal expected type for Stream.BodyTarget.Orbit.
noncomputable def PartACanonical.Types.p0799 :
(∀ (_v0 : (@Nat)),
(Sort 0)) := by
  exact @Stream.BodyTarget.Orbit

-- Independent literal expected type for Stream.RawTarget.AcceptedOrbit.
noncomputable def PartACanonical.Types.p0800 :
(∀ (_v0 : (@Nat)),
(Sort 0)) := by
  exact @Stream.RawTarget.AcceptedOrbit

-- Independent literal expected type for Stream.Target.Kernel.
noncomputable def PartACanonical.Types.p0801 :
(Sort 0) := by
  exact @Stream.Target.Kernel

-- Independent literal expected type for Stream.Target.PartA.
noncomputable def PartACanonical.Types.p0802 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Pnp3.Complexity.Uniform.V1.UniformTM))),
(∀ (_v1 : (∀ (_v1 : (@Nat)),
(@Nat))),
(Sort 0))) := by
  exact @Stream.Target.PartA

-- Independent literal expected type for Stream.Target.cursor.
noncomputable def PartACanonical.Types.p0803 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(@Nat)))) := by
  exact @Stream.Target.cursor

-- Independent literal expected type for Stream.Target.cursor.eq_1.
noncomputable def PartACanonical.Types.p0804 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@Stream.Target.cursor _v0 _v1 _v2) (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v2) _v1))))) := by
  exact @Stream.Target.cursor.eq_1

-- Complete literal proposition for Stream.Target.cursor.eq_1; original proof reused.
theorem PartACanonical.Surface.m0476 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@Stream.Target.cursor _v0 _v1 _v2) (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v2) _v1))))) := by
  exact @Stream.Target.cursor.eq_1

-- Independent literal expected type for Stream.Target.image.
noncomputable def PartACanonical.Types.p0805 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Bool)),
(∀ (_v8 : (@Nat)),
(@Option.{0} (@Bool))))))))))) := by
  exact @Stream.Target.image

-- Independent literal expected type for Stream.Target.image.eq_1.
noncomputable def PartACanonical.Types.p0806 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Bool)),
(∀ (_v8 : (@Nat)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Stream.Target.image _v0 _v1 _v2 _v3 _v4 _v5 _v6 _v7 _v8) (@ite.{(0 + 1)}
  (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v8) (@LT.lt.{0} (@Nat) (@instLTNat) _v8 (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat)))) _v3) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))
  (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v8) (@LT.lt.{0} (@Nat) (@instLTNat) _v8 (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat)))) _v3) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Nat.decLt
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v8)
  (@Nat.decLt _v8 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v3) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))))) (@Option.some.{0} (@Bool) (@GetElem?.getElem!.{0, 0, 0} (@List.{0} (@Bool)) (@Nat) (@Bool) (fun (_v9 :
  (@List.{0} (@Bool))) =>
(fun (_v10 : (@Nat)) =>
(@LT.lt.{0} (@Nat) (@instLTNat) _v10 (@List.length.{0} (@Bool) _v9)))) (@List.instGetElem?NatLtLength.{0} (@Bool))
  (@instInhabitedBool) (@Body.iterBits (@List.replicate.{0} (@Bool) _v3 (@Bool.false)) _v5) (@HSub.hSub.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v3) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v8))) (@ite.{(0 + 1)} (@Option.{0} (@Bool))
  (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v3) (@OfNat.ofNat.{0} (@Nat) (1
  : Nat) (@instOfNatNat (1 : Nat)))) _v8) (@LE.le.{0} (@Nat) (@instLENat) _v8 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v3) (@OfNat.ofNat.{0} (@Nat) (1
  : Nat) (@instOfNatNat (1 : Nat)))) _v6))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat)))) _v3) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v8) (@LE.le.{0} (@Nat) (@instLENat)
  _v8 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2
  : Nat)))) _v3) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v6)) (@Nat.decLt (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat)))) _v3) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v8) (@Nat.decLe _v8 (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v3) (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v6))) (@Option.some.{0} (@Bool) (@Bool.true)) (@ite.{(0 + 1)} (@Option.{0}
  (@Bool)) (@And (@Eq.{(0 + 1)} (@Bool) _v7 (@Bool.true)) (@And (@Eq.{(0 + 1)} (@Nat) _v8 (@Stream.Target.cursor _v4 _v1
  _v5)) (@LT.lt.{0} (@Nat) (@instLTNat) _v8 _v1))) (@instDecidableAnd (@Eq.{(0 + 1)} (@Bool) _v7 (@Bool.true)) (@And
  (@Eq.{(0 + 1)} (@Nat) _v8 (@Stream.Target.cursor _v4 _v1 _v5)) (@LT.lt.{0} (@Nat) (@instLTNat) _v8 _v1))
  (@instDecidableEqBool _v7 (@Bool.true)) (@instDecidableAnd (@Eq.{(0 + 1)} (@Nat) _v8 (@Stream.Target.cursor _v4 _v1
  _v5)) (@LT.lt.{0} (@Nat) (@instLTNat) _v8 _v1) (@instDecidableEqNat _v8 (@Stream.Target.cursor _v4 _v1 _v5)) (@Nat.decLt
  _v8 _v1))) (@Option.none.{0} (@Bool)) (@_v0 _v8)))))))))))))) := by
  exact @Stream.Target.image.eq_1

-- Complete literal proposition for Stream.Target.image.eq_1; original proof reused.
theorem PartACanonical.Surface.m0477 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Bool)),
(∀ (_v8 : (@Nat)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Stream.Target.image _v0 _v1 _v2 _v3 _v4 _v5 _v6 _v7 _v8) (@ite.{(0 + 1)}
  (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v8) (@LT.lt.{0} (@Nat) (@instLTNat) _v8 (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat)))) _v3) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))
  (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v8) (@LT.lt.{0} (@Nat) (@instLTNat) _v8 (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat)))) _v3) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Nat.decLt
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v8)
  (@Nat.decLt _v8 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v3) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))))) (@Option.some.{0} (@Bool) (@GetElem?.getElem!.{0, 0, 0} (@List.{0} (@Bool)) (@Nat) (@Bool) (fun (_v9 :
  (@List.{0} (@Bool))) =>
(fun (_v10 : (@Nat)) =>
(@LT.lt.{0} (@Nat) (@instLTNat) _v10 (@List.length.{0} (@Bool) _v9)))) (@List.instGetElem?NatLtLength.{0} (@Bool))
  (@instInhabitedBool) (@Body.iterBits (@List.replicate.{0} (@Bool) _v3 (@Bool.false)) _v5) (@HSub.hSub.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v3) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v8))) (@ite.{(0 + 1)} (@Option.{0} (@Bool))
  (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v3) (@OfNat.ofNat.{0} (@Nat) (1
  : Nat) (@instOfNatNat (1 : Nat)))) _v8) (@LE.le.{0} (@Nat) (@instLENat) _v8 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v3) (@OfNat.ofNat.{0} (@Nat) (1
  : Nat) (@instOfNatNat (1 : Nat)))) _v6))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat)))) _v3) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v8) (@LE.le.{0} (@Nat) (@instLENat)
  _v8 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2
  : Nat)))) _v3) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v6)) (@Nat.decLt (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat)))) _v3) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v8) (@Nat.decLe _v8 (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v3) (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v6))) (@Option.some.{0} (@Bool) (@Bool.true)) (@ite.{(0 + 1)} (@Option.{0}
  (@Bool)) (@And (@Eq.{(0 + 1)} (@Bool) _v7 (@Bool.true)) (@And (@Eq.{(0 + 1)} (@Nat) _v8 (@Stream.Target.cursor _v4 _v1
  _v5)) (@LT.lt.{0} (@Nat) (@instLTNat) _v8 _v1))) (@instDecidableAnd (@Eq.{(0 + 1)} (@Bool) _v7 (@Bool.true)) (@And
  (@Eq.{(0 + 1)} (@Nat) _v8 (@Stream.Target.cursor _v4 _v1 _v5)) (@LT.lt.{0} (@Nat) (@instLTNat) _v8 _v1))
  (@instDecidableEqBool _v7 (@Bool.true)) (@instDecidableAnd (@Eq.{(0 + 1)} (@Nat) _v8 (@Stream.Target.cursor _v4 _v1
  _v5)) (@LT.lt.{0} (@Nat) (@instLTNat) _v8 _v1) (@instDecidableEqNat _v8 (@Stream.Target.cursor _v4 _v1 _v5)) (@Nat.decLt
  _v8 _v1))) (@Option.none.{0} (@Bool)) (@_v0 _v8)))))))))))))) := by
  exact @Stream.Target.image.eq_1

-- Independent literal expected type for Stream.Target.mode.
noncomputable def PartACanonical.Types.p0807 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))))) := by
  exact @Stream.Target.mode

-- Independent literal expected type for Stream.Target.mode.eq_1.
noncomputable def PartACanonical.Types.p0808 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(@Eq.{(0 + 1)} (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Stream.Target.mode _v0 _v1 _v2)
  (@ite.{(0 + 1)} (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Eq.{(0 + 1)} (@Nat) _v1 _v2)
  (@instDecidableEqNat _v1 _v2) (@Fin.mk (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@Stream.Target.mode._proof_1)) (@ite.{(0 + 1)} (@Fin (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v0 _v1) (@Option.some.{0} (@Bool)
  (@Bool.true))) (@Option.instDecidableEq.{0} (@Bool) (@instDecidableEqBool) (@_v0 _v1) (@Option.some.{0} (@Bool)
  (@Bool.true))) (@Fin.mk (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))) (@Stream.Target.mode._proof_2)) (@Fin.mk (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Stream.Target.mode._proof_3)))))))) := by
  exact @Stream.Target.mode.eq_1

-- Complete literal proposition for Stream.Target.mode.eq_1; original proof reused.
theorem PartACanonical.Surface.m0478 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(@Eq.{(0 + 1)} (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Stream.Target.mode _v0 _v1 _v2)
  (@ite.{(0 + 1)} (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Eq.{(0 + 1)} (@Nat) _v1 _v2)
  (@instDecidableEqNat _v1 _v2) (@Fin.mk (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@Stream.Target.mode._proof_1)) (@ite.{(0 + 1)} (@Fin (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v0 _v1) (@Option.some.{0} (@Bool)
  (@Bool.true))) (@Option.instDecidableEq.{0} (@Bool) (@instDecidableEqBool) (@_v0 _v1) (@Option.some.{0} (@Bool)
  (@Bool.true))) (@Fin.mk (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))) (@Stream.Target.mode._proof_2)) (@Fin.mk (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Stream.Target.mode._proof_3)))))))) := by
  exact @Stream.Target.mode.eq_1

-- Independent literal expected type for Stream.accepted_budget.
noncomputable def PartACanonical.Types.p0809 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ {_v3 : (@Nat)},
(∀ (_v4 : (@Eq.{(0 + 1)} (@Nat) _v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v5 : (@LE.le.{0} (@Nat) (@instLENat) _v2 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 _v1))),
(∀ (_v6 : (@LE.le.{0} (@Nat) (@instLENat) _v3 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 _v1))),
(@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1)
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v0 _v1) _v2) _v3) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))))
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))))))))) := by
  exact @Stream.accepted_budget

-- Complete literal proposition for Stream.accepted_budget; original proof reused.
theorem PartACanonical.Surface.m0479 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ {_v3 : (@Nat)},
(∀ (_v4 : (@Eq.{(0 + 1)} (@Nat) _v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v5 : (@LE.le.{0} (@Nat) (@instLENat) _v2 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 _v1))),
(∀ (_v6 : (@LE.le.{0} (@Nat) (@instLENat) _v3 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 _v1))),
(@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1)
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v0 _v1) _v2) _v3) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))))
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))))))))) := by
  exact @Stream.accepted_budget

-- Independent literal expected type for Stream.accepted_rows_fit.
noncomputable def PartACanonical.Types.p0810 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ {_v3 : (@Nat)},
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v5 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v2)),
(∀ (_v6 : (@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v1
  _v2 _v4 _v5) (@Bool.true))),
(∀ {_v7 : (@AcceptedBody.Parsed _v0)},
(∀ (_v8 : (@Eq.{(0 + 1)} (@Option.{0} (@Sigma.{0, 0} (@Nat) (fun (_v8 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v8))))) (@Pnp4.Frontier.ContractExpansion.contentInput?
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v4 _v5)) (@Option.some.{0} (@AcceptedBody.Parsed _v0)
  _v7))),
(∀ (_v9 : (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros?
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2
  (@Bool) _v4 _v5)) (@Option.some.{0} (@Nat) _v3))),
(@LE.le.{0} (@Nat) (@instLENat) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v10))) _v7)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v10 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v10))) _v7))) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHSub.{0} (@Nat) (@instSubNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat))
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v3)
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v10))) _v7)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v10 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v10))) _v7))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat
  (3 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))))))))))) := by
  exact @Stream.accepted_rows_fit

-- Complete literal proposition for Stream.accepted_rows_fit; original proof reused.
theorem PartACanonical.Surface.m0480 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ {_v3 : (@Nat)},
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v5 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v2)),
(∀ (_v6 : (@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v1
  _v2 _v4 _v5) (@Bool.true))),
(∀ {_v7 : (@AcceptedBody.Parsed _v0)},
(∀ (_v8 : (@Eq.{(0 + 1)} (@Option.{0} (@Sigma.{0, 0} (@Nat) (fun (_v8 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v8))))) (@Pnp4.Frontier.ContractExpansion.contentInput?
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v4 _v5)) (@Option.some.{0} (@AcceptedBody.Parsed _v0)
  _v7))),
(∀ (_v9 : (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros?
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2
  (@Bool) _v4 _v5)) (@Option.some.{0} (@Nat) _v3))),
(@LE.le.{0} (@Nat) (@instLENat) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v10))) _v7)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v10 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v10))) _v7))) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHSub.{0} (@Nat) (@instSubNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat))
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v3)
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v10))) _v7)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v10 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v10))) _v7))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat
  (3 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))))))))))) := by
  exact @Stream.accepted_rows_fit

-- Independent literal expected type for Stream.kernel.
noncomputable def PartACanonical.Types.p0811 :
(@Stream.Target.Kernel) := by
  exact @Stream.kernel

-- Complete literal proposition for Stream.kernel; original proof reused.
theorem PartACanonical.Surface.m0481 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (∀ (_v7 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v8 : (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v5)),
(∀ (_v9 : (@LE.le.{0} (@Nat) (@instLENat) _v5 _v2)),
(∀ (_v10 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v3) _v4) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) _v6)),
(∀ (_v11 : (@LT.lt.{0} (@Nat) (@instLTNat) _v6 (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))),
(∀ (_v12 : (∀ (_v12 : (@Nat)),
(∀ (_v13 : (@LE.le.{0} (@Nat) (@instLENat) _v5 _v12)),
(∀ (_v14 : (@LT.lt.{0} (@Nat) (@instLTNat) _v12 _v2)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v15 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v7 _v12) (@Option.some.{0} (@Bool) _v15)))))))),
(∀ (_v13 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v7 _v2) (@Option.none.{0} (@Bool)))),
(∀ (_v14 : (∀ (_v14 : (@Nat)),
(∀ (_v15 : (@LT.lt.{0} (@Nat) (@instLTNat) _v2 _v14)),
(∀ (_v16 : (@LT.lt.{0} (@Nat) (@instLTNat) _v14 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v3)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v7 _v14) (@Option.some.{0} (@Bool) (@Bool.false))))))),
(∀ (_v15 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v7 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v3)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))) (@Option.none.{0} (@Bool)))),
(∀ (_v16 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v7 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v3) _v4) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))))) (@Option.none.{0} (@Bool)))),
(∀ (_v17 : (∀ (_v17 : (@Nat)),
(∀ (_v18 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v3) _v4) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) _v17)),
(∀ (_v19 : (@LT.lt.{0} (@Nat) (@instLTNat) _v17 _v6)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v7 _v17) (@Option.none.{0} (@Bool))))))),
(∀ (_v18 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v7 _v6) (@Option.some.{0} (@Bool) (@Bool.false)))),
(let _v19 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v2 _v3) _v4) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))));
(let _v20 : (@Nat) := (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HSub.hSub.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v6 _v19) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat))));
(let _v21 : (@Nat) := (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v4) _v20);
(∀ (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat) _v19 (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))),
(let _v23 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Stream.machine)) _v0
  _v1) := (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Stream.machine)) _v0
  _v1 (@Stream.unpaid (@Stream.Target.mode _v7 _v5 _v2)) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v19
  _v22) (fun (_v23 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))) =>
(@Stream.Target.image _v7 _v2 _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Bool.true) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v23))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v24 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v24 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))) (@And (∀ (_v25 : (@Nat)),
(∀ (_v26 : (@LT.lt.{0} (@Nat) (@instLTNat) _v25 _v21)),
(@Exists.{(0 + 1)} (@Nat) (fun (_v27 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v27 _v24) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Stream.machine)) _v0 _v1) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@Stream.machine) _v0 _v1 _v27 _v23) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Stream.machine)) _v0 _v1 (@Stream.paid (@Stream.Target.mode _v7
  (@Stream.Target.cursor _v5 _v2 _v25) _v2)) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v19 _v22) (fun
  (_v28 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))) =>
(@Stream.Target.image _v7 _v2 _v3 _v4 _v5 _v25 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v25 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Bool.true) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v28)))))))))) (@ite.{(0 + 1)} (Sort 0) (@LE.le.{0} (@Nat) (@instLENat)
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4) _v20) (@Nat.decLe (@HPow.hPow.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid)))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4) _v20) (@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat)
  (@Stream.Target.cursor _v5 _v2 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (fun (_v25 : (@LT.lt.{0} (@Nat) (@instLTNat) (@Stream.Target.cursor
  _v5 _v2 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))) =>
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Stream.machine))
  _v0 _v1) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Stream.machine) _v0 _v1 _v24 _v23)
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Stream.machine)) _v0 _v1
  (@Stream.q (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Stream.Target.cursor _v5 _v2 (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)) _v2) (@instDecidableEqNat (@Stream.Target.cursor _v5 _v2 (@HPow.hPow.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid)))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (57 : Nat)
  (@instOfNatNat (57 : Nat))) (@OfNat.ofNat.{0} (@Nat) (58 : Nat) (@instOfNatNat (58 : Nat))))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) (@Stream.Target.cursor _v5 _v2 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))) _v4)) _v25) (fun (_v26 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))) =>
(@Stream.Target.image _v7 _v2 _v3 _v4 _v5 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4) (@Bool.false) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v26))))))) (@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) _v6
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (fun (_v25 : (@LT.lt.{0} (@Nat) (@instLTNat) _v6
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))) =>
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Stream.machine))
  _v0 _v1) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Stream.machine) _v0 _v1 _v24 _v23)
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Stream.machine)) _v0 _v1
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@Stream.machine)) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v0
  _v1) _v6 _v25) (fun (_v26 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))) =>
(@Stream.Target.image _v7 _v2 _v3 _v4 _v5 _v20 _v20 (@Bool.true) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0
  _v1) _v26)))))))))))))))))))))))))))))))))))) := by
  exact @Stream.kernel

-- Independent literal expected type for Stream.machine.
noncomputable def PartACanonical.Types.p0812 :
(@Pnp3.Complexity.Uniform.V1.UniformTM) := by
  exact @Stream.machine

-- Independent literal expected type for Stream.machine.eq_1.
noncomputable def PartACanonical.Types.p0813 :
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.UniformTM) (@Stream.machine) (@Pnp3.Complexity.Uniform.V1.UniformTM.mk
  (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) (@Stream.q (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))) (@Stream.q (@OfNat.ofNat.{0} (@Nat) (39 : Nat) (@instOfNatNat (39 : Nat)))) (@Stream.q
  (@OfNat.ofNat.{0} (@Nat) (40 : Nat) (@instOfNatNat (40 : Nat)))) (@Stream.machine._proof_1) (@Stream.rows))) := by
  exact @Stream.machine.eq_1

-- Complete literal proposition for Stream.machine.eq_1; original proof reused.
theorem PartACanonical.Surface.m0482 :
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.UniformTM) (@Stream.machine) (@Pnp3.Complexity.Uniform.V1.UniformTM.mk
  (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) (@Stream.q (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))) (@Stream.q (@OfNat.ofNat.{0} (@Nat) (39 : Nat) (@instOfNatNat (39 : Nat)))) (@Stream.q
  (@OfNat.ofNat.{0} (@Nat) (40 : Nat) (@instOfNatNat (40 : Nat)))) (@Stream.machine._proof_1) (@Stream.rows))) := by
  exact @Stream.machine.eq_1

-- Independent literal expected type for Stream.paid.
noncomputable def PartACanonical.Types.p0814 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))))) := by
  exact @Stream.paid

-- Independent literal expected type for Stream.q.
noncomputable def PartACanonical.Types.p0815 :
(∀ (_v0 : (@Nat)),
(@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))))) := by
  exact @Stream.q

-- Independent literal expected type for Stream.q.eq_1.
noncomputable def PartACanonical.Types.p0816 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Stream.q _v0) (@Fin.mk
  (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) (@HMod.hMod.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMod.{0} (@Nat) (@Nat.instMod)) _v0 (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))))
  (@Stream.q._proof_1 _v0)))) := by
  exact @Stream.q.eq_1

-- Complete literal proposition for Stream.q.eq_1; original proof reused.
theorem PartACanonical.Surface.m0483 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat)))) (@Stream.q _v0) (@Fin.mk
  (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) (@HMod.hMod.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMod.{0} (@Nat) (@Nat.instMod)) _v0 (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))))
  (@Stream.q._proof_1 _v0)))) := by
  exact @Stream.q.eq_1

-- Independent literal expected type for Stream.rawMachine.
noncomputable def PartACanonical.Types.p0817 :
(@Pnp3.Complexity.Uniform.V1.UniformTM) := by
  exact @Stream.rawMachine
