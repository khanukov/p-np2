import Tests.PartACanonicalABI
import Tests.PartAG2InterfaceTests

/-! Infrastructure: mechanical literal restatements of this exact original API.
Proof terms are reused; these are not independently authored correctness proofs.
Type pins, theorem mirrors and direct roots remain separate manifests. -/
set_option autoImplicit false

-- Independent literal expected type for Cursor.Target.W.eq_1.
noncomputable def PartACanonical.Types.p0321 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@Cursor.Target.W _v0 _v1) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp4.Frontier.ContractExpansion.bitLength _v1) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v1 _v0) _v0))))) := by
  exact @Cursor.Target.W.eq_1

-- Complete literal proposition for Cursor.Target.W.eq_1; original proof reused.
theorem PartACanonical.Surface.m0200 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@Cursor.Target.W _v0 _v1) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp4.Frontier.ContractExpansion.bitLength _v1) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v1 _v0) _v0))))) := by
  exact @Cursor.Target.W.eq_1

-- Independent literal expected type for Cursor.Target.deadline.
noncomputable def PartACanonical.Types.p0322 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(@Nat))) := by
  exact @Cursor.Target.deadline

-- Independent literal expected type for Cursor.Target.image.
noncomputable def PartACanonical.Types.p0323 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(@Option.{0} (@Bool))))))))) := by
  exact @Cursor.Target.image

-- Independent literal expected type for Cursor.Target.image.eq_1.
noncomputable def PartACanonical.Types.p0324 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Cursor.Target.image _v0 _v1 _v2 _v3 _v4 _v5 _v6) (@ite.{(0 + 1)} (@Option.{0}
  (@Bool)) (@And (@Eq.{(0 + 1)} (@Nat) _v6 (@Cursor.Target.M _v1 _v3 _v4)) (@LT.lt.{0} (@Nat) (@instLTNat) _v6 _v2))
  (@instDecidableAnd (@Eq.{(0 + 1)} (@Nat) _v6 (@Cursor.Target.M _v1 _v3 _v4)) (@LT.lt.{0} (@Nat) (@instLTNat) _v6 _v2)
  (@instDecidableEqNat _v6 (@Cursor.Target.M _v1 _v3 _v4)) (@Nat.decLt _v6 _v2)) (@Option.none.{0} (@Bool)) (@ite.{(0 +
  1)} (∀ (_v7 : (@Nat)),
(@Option.{0} (@Bool))) (@LT.lt.{0} (@Nat) (@instLTNat) (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4))
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v3)) _v2) _v2) (@Nat.decLt
  (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat)
  (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v3)) _v2) _v2) (@Cursor.Target.scratch _v0 _v5 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHSub.{0} (@Nat) (@instSubNat)) _v2 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)) (@HPow.hPow.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid)))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v3)) _v2)) _v3) _v0 _v6)))))))))) := by
  exact @Cursor.Target.image.eq_1

-- Complete literal proposition for Cursor.Target.image.eq_1; original proof reused.
theorem PartACanonical.Surface.m0201 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Cursor.Target.image _v0 _v1 _v2 _v3 _v4 _v5 _v6) (@ite.{(0 + 1)} (@Option.{0}
  (@Bool)) (@And (@Eq.{(0 + 1)} (@Nat) _v6 (@Cursor.Target.M _v1 _v3 _v4)) (@LT.lt.{0} (@Nat) (@instLTNat) _v6 _v2))
  (@instDecidableAnd (@Eq.{(0 + 1)} (@Nat) _v6 (@Cursor.Target.M _v1 _v3 _v4)) (@LT.lt.{0} (@Nat) (@instLTNat) _v6 _v2)
  (@instDecidableEqNat _v6 (@Cursor.Target.M _v1 _v3 _v4)) (@Nat.decLt _v6 _v2)) (@Option.none.{0} (@Bool)) (@ite.{(0 +
  1)} (∀ (_v7 : (@Nat)),
(@Option.{0} (@Bool))) (@LT.lt.{0} (@Nat) (@instLTNat) (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4))
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v3)) _v2) _v2) (@Nat.decLt
  (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat)
  (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v3)) _v2) _v2) (@Cursor.Target.scratch _v0 _v5 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHSub.{0} (@Nat) (@instSubNat)) _v2 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)) (@HPow.hPow.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid)))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v3)) _v2)) _v3) _v0 _v6)))))))))) := by
  exact @Cursor.Target.image.eq_1

-- Independent literal expected type for Cursor.Target.scratch.
noncomputable def PartACanonical.Types.p0325 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(@Option.{0} (@Bool))))))) := by
  exact @Cursor.Target.scratch

-- Independent literal expected type for Cursor.Target.scratch.eq_1.
noncomputable def PartACanonical.Types.p0326 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Cursor.Target.scratch _v0 _v1 _v2 _v3 _v4) (@ite.{(0 + 1)} (@Option.{0} (@Bool))
  (@Or (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v4) (@LT.lt.{0} (@Nat) (@instLTNat)
  _v4 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))))
  (@Or (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v4) (@LT.lt.{0} (@Nat) (@instLTNat) _v4 (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  _v2) _v3) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))))) (@Or (@And (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 _v2) _v3) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v4) (@LT.lt.{0} (@Nat)
  (@instLTNat) _v4 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))))) (@Or (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v2)) _v3)
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v4) (@LT.lt.{0} (@Nat) (@instLTNat) _v4 (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))) (@Or (@And
  (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (5 :
  Nat) (@instOfNatNat (5 : Nat)))) _v4) (@LT.lt.{0} (@Nat) (@instLTNat) _v4 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v2)) _v3)
  (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))) (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) _v4) (@LT.lt.{0}
  (@Nat) (@instLTNat) _v4 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (7 : Nat)
  (@instOfNatNat (7 : Nat))))))))))) (@instDecidableOr (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  _v4) (@LT.lt.{0} (@Nat) (@instLTNat) _v4 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat)))))) (@Or (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  _v2) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v4) (@LT.lt.{0} (@Nat) (@instLTNat) _v4
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 _v2) _v3) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))))) (@Or (@And (@LT.lt.{0}
  (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v2) _v3) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v4) (@LT.lt.{0}
  (@Nat) (@instLTNat) _v4 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))))) (@Or (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v2)) _v3)
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v4) (@LT.lt.{0} (@Nat) (@instLTNat) _v4 (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))) (@Or (@And
  (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (5 :
  Nat) (@instOfNatNat (5 : Nat)))) _v4) (@LT.lt.{0} (@Nat) (@instLTNat) _v4 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v2)) _v3)
  (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))) (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) _v4) (@LT.lt.{0}
  (@Nat) (@instLTNat) _v4 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (7 : Nat)
  (@instOfNatNat (7 : Nat)))))))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v4)
  (@LT.lt.{0} (@Nat) (@instLTNat) _v4 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))))) (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v4) (@Nat.decLt _v4 (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))))
  (@instDecidableOr (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v4) (@LT.lt.{0} (@Nat) (@instLTNat) _v4 (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  _v2) _v3) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))))) (@Or (@And (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 _v2) _v3) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v4) (@LT.lt.{0} (@Nat)
  (@instLTNat) _v4 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))))) (@Or (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v2)) _v3)
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v4) (@LT.lt.{0} (@Nat) (@instLTNat) _v4 (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))) (@Or (@And
  (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (5 :
  Nat) (@instOfNatNat (5 : Nat)))) _v4) (@LT.lt.{0} (@Nat) (@instLTNat) _v4 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v2)) _v3)
  (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))) (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) _v4) (@LT.lt.{0}
  (@Nat) (@instLTNat) _v4 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (7 : Nat)
  (@instOfNatNat (7 : Nat))))))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v4) (@LT.lt.{0} (@Nat)
  (@instLTNat) _v4 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v2) _v3) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))) (@Nat.decLt
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v4)
  (@Nat.decLt _v4 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v2) _v3) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))))) (@instDecidableOr
  (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v3) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))
  _v4) (@LT.lt.{0} (@Nat) (@instLTNat) _v4 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))))) (@Or (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v2)) _v3)
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v4) (@LT.lt.{0} (@Nat) (@instLTNat) _v4 (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))) (@Or (@And
  (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (5 :
  Nat) (@instOfNatNat (5 : Nat)))) _v4) (@LT.lt.{0} (@Nat) (@instLTNat) _v4 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v2)) _v3)
  (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))) (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) _v4) (@LT.lt.{0}
  (@Nat) (@instLTNat) _v4 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (7 : Nat)
  (@instOfNatNat (7 : Nat)))))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v3)
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v4) (@LT.lt.{0} (@Nat) (@instLTNat) _v4 (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@Nat.decLt
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 _v2) _v3) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v4) (@Nat.decLt _v4
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))))
  (@instDecidableOr (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))) _v4) (@LT.lt.{0} (@Nat) (@instLTNat) _v4 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))
  _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))) (@Or (@And (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))
  _v4) (@LT.lt.{0} (@Nat) (@instLTNat) _v4 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (6 :
  Nat) (@instOfNatNat (6 : Nat)))))) (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v2)) _v3)
  (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) _v4) (@LT.lt.{0} (@Nat) (@instLTNat) _v4 (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat)
  (@instOfNatNat (5 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))))))
  (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))) _v4) (@LT.lt.{0} (@Nat) (@instLTNat) _v4 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))
  _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))) (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v4) (@Nat.decLt _v4 (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))) (@instDecidableOr
  (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (5 :
  Nat) (@instOfNatNat (5 : Nat)))) _v4) (@LT.lt.{0} (@Nat) (@instLTNat) _v4 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v2)) _v3)
  (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))) (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) _v4) (@LT.lt.{0}
  (@Nat) (@instLTNat) _v4 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (7 : Nat)
  (@instOfNatNat (7 : Nat)))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))
  _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) _v4) (@LT.lt.{0} (@Nat) (@instLTNat) _v4
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))
  (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))
  _v4) (@Nat.decLt _v4 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (6 : Nat)
  (@instOfNatNat (6 : Nat)))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))
  _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) _v4) (@LT.lt.{0} (@Nat) (@instLTNat) _v4
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))))
  (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))
  _v4) (@Nat.decLt _v4 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (7 : Nat)
  (@instOfNatNat (7 : Nat))))))))))) (@Option.some.{0} (@Bool) (@Bool.false)) (@_v0 _v4)))))))) := by
  exact @Cursor.Target.scratch.eq_1

-- Complete literal proposition for Cursor.Target.scratch.eq_1; original proof reused.
theorem PartACanonical.Surface.m0202 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Cursor.Target.scratch _v0 _v1 _v2 _v3 _v4) (@ite.{(0 + 1)} (@Option.{0} (@Bool))
  (@Or (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v4) (@LT.lt.{0} (@Nat) (@instLTNat)
  _v4 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))))
  (@Or (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v4) (@LT.lt.{0} (@Nat) (@instLTNat) _v4 (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  _v2) _v3) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))))) (@Or (@And (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 _v2) _v3) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v4) (@LT.lt.{0} (@Nat)
  (@instLTNat) _v4 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))))) (@Or (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v2)) _v3)
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v4) (@LT.lt.{0} (@Nat) (@instLTNat) _v4 (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))) (@Or (@And
  (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (5 :
  Nat) (@instOfNatNat (5 : Nat)))) _v4) (@LT.lt.{0} (@Nat) (@instLTNat) _v4 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v2)) _v3)
  (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))) (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) _v4) (@LT.lt.{0}
  (@Nat) (@instLTNat) _v4 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (7 : Nat)
  (@instOfNatNat (7 : Nat))))))))))) (@instDecidableOr (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  _v4) (@LT.lt.{0} (@Nat) (@instLTNat) _v4 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat)))))) (@Or (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  _v2) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v4) (@LT.lt.{0} (@Nat) (@instLTNat) _v4
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 _v2) _v3) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))))) (@Or (@And (@LT.lt.{0}
  (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v2) _v3) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v4) (@LT.lt.{0}
  (@Nat) (@instLTNat) _v4 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))))) (@Or (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v2)) _v3)
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v4) (@LT.lt.{0} (@Nat) (@instLTNat) _v4 (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))) (@Or (@And
  (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (5 :
  Nat) (@instOfNatNat (5 : Nat)))) _v4) (@LT.lt.{0} (@Nat) (@instLTNat) _v4 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v2)) _v3)
  (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))) (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) _v4) (@LT.lt.{0}
  (@Nat) (@instLTNat) _v4 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (7 : Nat)
  (@instOfNatNat (7 : Nat)))))))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v4)
  (@LT.lt.{0} (@Nat) (@instLTNat) _v4 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))))) (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v4) (@Nat.decLt _v4 (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))))
  (@instDecidableOr (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v4) (@LT.lt.{0} (@Nat) (@instLTNat) _v4 (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  _v2) _v3) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))))) (@Or (@And (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 _v2) _v3) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v4) (@LT.lt.{0} (@Nat)
  (@instLTNat) _v4 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))))) (@Or (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v2)) _v3)
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v4) (@LT.lt.{0} (@Nat) (@instLTNat) _v4 (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))) (@Or (@And
  (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (5 :
  Nat) (@instOfNatNat (5 : Nat)))) _v4) (@LT.lt.{0} (@Nat) (@instLTNat) _v4 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v2)) _v3)
  (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))) (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) _v4) (@LT.lt.{0}
  (@Nat) (@instLTNat) _v4 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (7 : Nat)
  (@instOfNatNat (7 : Nat))))))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v4) (@LT.lt.{0} (@Nat)
  (@instLTNat) _v4 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v2) _v3) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))) (@Nat.decLt
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v4)
  (@Nat.decLt _v4 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v2) _v3) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))))) (@instDecidableOr
  (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v3) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))
  _v4) (@LT.lt.{0} (@Nat) (@instLTNat) _v4 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))))) (@Or (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v2)) _v3)
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v4) (@LT.lt.{0} (@Nat) (@instLTNat) _v4 (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))) (@Or (@And
  (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (5 :
  Nat) (@instOfNatNat (5 : Nat)))) _v4) (@LT.lt.{0} (@Nat) (@instLTNat) _v4 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v2)) _v3)
  (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))) (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) _v4) (@LT.lt.{0}
  (@Nat) (@instLTNat) _v4 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (7 : Nat)
  (@instOfNatNat (7 : Nat)))))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v3)
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v4) (@LT.lt.{0} (@Nat) (@instLTNat) _v4 (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@Nat.decLt
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 _v2) _v3) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v4) (@Nat.decLt _v4
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))))
  (@instDecidableOr (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))) _v4) (@LT.lt.{0} (@Nat) (@instLTNat) _v4 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))
  _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))) (@Or (@And (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))
  _v4) (@LT.lt.{0} (@Nat) (@instLTNat) _v4 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (6 :
  Nat) (@instOfNatNat (6 : Nat)))))) (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v2)) _v3)
  (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) _v4) (@LT.lt.{0} (@Nat) (@instLTNat) _v4 (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat)
  (@instOfNatNat (5 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))))))
  (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))) _v4) (@LT.lt.{0} (@Nat) (@instLTNat) _v4 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))
  _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))) (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v4) (@Nat.decLt _v4 (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))) (@instDecidableOr
  (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (5 :
  Nat) (@instOfNatNat (5 : Nat)))) _v4) (@LT.lt.{0} (@Nat) (@instLTNat) _v4 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v2)) _v3)
  (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))) (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) _v4) (@LT.lt.{0}
  (@Nat) (@instLTNat) _v4 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (7 : Nat)
  (@instOfNatNat (7 : Nat)))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))
  _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) _v4) (@LT.lt.{0} (@Nat) (@instLTNat) _v4
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))
  (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))
  _v4) (@Nat.decLt _v4 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (6 : Nat)
  (@instOfNatNat (6 : Nat)))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))
  _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) _v4) (@LT.lt.{0} (@Nat) (@instLTNat) _v4
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))))
  (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))
  _v4) (@Nat.decLt _v4 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v2)) _v3) (@OfNat.ofNat.{0} (@Nat) (7 : Nat)
  (@instOfNatNat (7 : Nat))))))))))) (@Option.some.{0} (@Bool) (@Bool.false)) (@_v0 _v4)))))))) := by
  exact @Cursor.Target.scratch.eq_1

-- Independent literal expected type for Cursor.Transport.avoid_changed_rows.
noncomputable def PartACanonical.Types.p0327 :
(∀ (_v0 : (@Pnp3.Complexity.Uniform.V1.UniformTM)),
(∀ (_v1 : (@Pnp3.Complexity.Uniform.V1.UniformTM)),
(∀ (_v2 : (∀ (_v2 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0))),
(@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v1)))),
(∀ (_v3 : (∀ (_v3 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0))),
(Sort 0))),
(∀ (_v4 : (∀ {_v4 : (@Nat)},
(∀ {_v5 : (@Nat)},
(∀ (_v6 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v4 _v5)),
(∀ (_v7 : (@_v3 (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v4 _v5
  _v6))),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v4 _v5)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stepConfig _v0 _v4 _v5 _v6) _v6)))))),
(∀ (_v5 : (∀ (_v5 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0))),
(∀ (_v6 : (@Not (@_v3 _v5))),
(∀ (_v7 : (@Option.{0} (@Bool))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v1)) (@Prod.{0, 0} (@Option.{0}
  (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step _v1 (@_v2 _v5) _v7)
  (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v1)) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@_v2 (@Prod.fst.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  _v0)) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.step _v0 _v5 _v7))) (@Prod.snd.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step _v0 _v5 _v7)))))))),
(∀ {_v6 : (@Nat)},
(∀ {_v7 : (@Nat)},
(∀ (_v8 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v6 _v7)),
(∀ (_v9 : (@Nat)),
(∀ (_v10 : (@Not (@_v3 (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)
  _v6 _v7 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v6 _v7 _v9 _v8))))),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v1) _v6 _v7)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v1 _v6 _v7 _v9 (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v1) _v6 _v7 (@_v2 (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v6 _v7 _v8)) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v6 _v7 _v8) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v6 _v7 _v8))) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v1) _v6 _v7 (@_v2 (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v6 _v7 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v6 _v7
  _v9 _v8))) (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v6 _v7
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v6 _v7 _v9 _v8)) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v6 _v7 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v6 _v7
  _v9 _v8))))))))))))))) := by
  exact @Cursor.Transport.avoid_changed_rows

-- Complete literal proposition for Cursor.Transport.avoid_changed_rows; original proof reused.
theorem PartACanonical.Surface.m0203 :
(∀ (_v0 : (@Pnp3.Complexity.Uniform.V1.UniformTM)),
(∀ (_v1 : (@Pnp3.Complexity.Uniform.V1.UniformTM)),
(∀ (_v2 : (∀ (_v2 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0))),
(@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v1)))),
(∀ (_v3 : (∀ (_v3 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0))),
(Sort 0))),
(∀ (_v4 : (∀ {_v4 : (@Nat)},
(∀ {_v5 : (@Nat)},
(∀ (_v6 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v4 _v5)),
(∀ (_v7 : (@_v3 (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v4 _v5
  _v6))),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v4 _v5)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stepConfig _v0 _v4 _v5 _v6) _v6)))))),
(∀ (_v5 : (∀ (_v5 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0))),
(∀ (_v6 : (@Not (@_v3 _v5))),
(∀ (_v7 : (@Option.{0} (@Bool))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v1)) (@Prod.{0, 0} (@Option.{0}
  (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step _v1 (@_v2 _v5) _v7)
  (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v1)) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@_v2 (@Prod.fst.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  _v0)) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.step _v0 _v5 _v7))) (@Prod.snd.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step _v0 _v5 _v7)))))))),
(∀ {_v6 : (@Nat)},
(∀ {_v7 : (@Nat)},
(∀ (_v8 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v6 _v7)),
(∀ (_v9 : (@Nat)),
(∀ (_v10 : (@Not (@_v3 (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)
  _v6 _v7 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v6 _v7 _v9 _v8))))),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v1) _v6 _v7)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v1 _v6 _v7 _v9 (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v1) _v6 _v7 (@_v2 (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v6 _v7 _v8)) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v6 _v7 _v8) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v6 _v7 _v8))) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v1) _v6 _v7 (@_v2 (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v6 _v7 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v6 _v7
  _v9 _v8))) (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v6 _v7
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v6 _v7 _v9 _v8)) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v6 _v7 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v6 _v7
  _v9 _v8))))))))))))))) := by
  exact @Cursor.Transport.avoid_changed_rows

-- Independent literal expected type for Cursor.Transport.first_changed_rows.
noncomputable def PartACanonical.Types.p0328 :
(∀ (_v0 : (@Pnp3.Complexity.Uniform.V1.UniformTM)),
(∀ (_v1 : (@Pnp3.Complexity.Uniform.V1.UniformTM)),
(∀ (_v2 : (∀ (_v2 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0))),
(@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v1)))),
(∀ (_v3 : (∀ (_v3 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0))),
(Sort 0))),
(∀ (_v4 : (∀ {_v4 : (@Nat)},
(∀ {_v5 : (@Nat)},
(∀ (_v6 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v4 _v5)),
(∀ (_v7 : (@_v3 (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v4 _v5
  _v6))),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v4 _v5)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stepConfig _v0 _v4 _v5 _v6) _v6)))))),
(∀ (_v5 : (∀ (_v5 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0))),
(∀ (_v6 : (@Not (@_v3 _v5))),
(∀ (_v7 : (@Option.{0} (@Bool))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v1)) (@Prod.{0, 0} (@Option.{0}
  (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step _v1 (@_v2 _v5) _v7)
  (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v1)) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@_v2 (@Prod.fst.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  _v0)) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.step _v0 _v5 _v7))) (@Prod.snd.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step _v0 _v5 _v7)))))))),
(∀ {_v6 : (@Nat)},
(∀ {_v7 : (@Nat)},
(∀ (_v8 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v6 _v7)),
(∀ (_v9 : (@Nat)),
(∀ (_v10 : (@_v3 (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v6
  _v7 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v6 _v7 _v9 _v8)))),
(@Exists.{(0 + 1)} (@Nat) (fun (_v11 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v11 _v9) (@And (∀ (_v12 : (@Nat)),
(∀ (_v13 : (@LT.lt.{0} (@Nat) (@instLTNat) _v12 _v11)),
(@Not (@_v3 (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v6 _v7
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v6 _v7 _v12 _v8)))))) (@And (@Eq.{(0 + 1)}
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v6 _v7)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v6 _v7 _v11 _v8) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v6 _v7
  _v9 _v8)) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  _v1) _v6 _v7) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v1 _v6 _v7 _v11 (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v1) _v6 _v7 (@_v2 (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v6 _v7 _v8)) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v6 _v7 _v8) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v6 _v7 _v8))) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v1) _v6 _v7 (@_v2 (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v6 _v7 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v6 _v7
  _v9 _v8))) (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v6 _v7
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v6 _v7 _v9 _v8)) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v6 _v7 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v6 _v7
  _v9 _v8)))) (∀ (_v12 : (@Nat)),
(∀ (_v13 : (@LE.le.{0} (@Nat) (@instLENat) _v12 _v11)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v1) _v6 _v7)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v1 _v6 _v7 _v12 (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v1) _v6 _v7 (@_v2 (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v6 _v7 _v8)) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v6 _v7 _v8) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v6 _v7 _v8))) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v1) _v6 _v7 (@_v2 (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v6 _v7 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v6 _v7
  _v12 _v8))) (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v6 _v7
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v6 _v7 _v12 _v8)) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v6 _v7 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v6 _v7
  _v12 _v8))))))))))))))))))))))) := by
  exact @Cursor.Transport.first_changed_rows

-- Complete literal proposition for Cursor.Transport.first_changed_rows; original proof reused.
theorem PartACanonical.Surface.m0204 :
(∀ (_v0 : (@Pnp3.Complexity.Uniform.V1.UniformTM)),
(∀ (_v1 : (@Pnp3.Complexity.Uniform.V1.UniformTM)),
(∀ (_v2 : (∀ (_v2 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0))),
(@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v1)))),
(∀ (_v3 : (∀ (_v3 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0))),
(Sort 0))),
(∀ (_v4 : (∀ {_v4 : (@Nat)},
(∀ {_v5 : (@Nat)},
(∀ (_v6 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v4 _v5)),
(∀ (_v7 : (@_v3 (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v4 _v5
  _v6))),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v4 _v5)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stepConfig _v0 _v4 _v5 _v6) _v6)))))),
(∀ (_v5 : (∀ (_v5 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0))),
(∀ (_v6 : (@Not (@_v3 _v5))),
(∀ (_v7 : (@Option.{0} (@Bool))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v1)) (@Prod.{0, 0} (@Option.{0}
  (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step _v1 (@_v2 _v5) _v7)
  (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v1)) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@_v2 (@Prod.fst.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  _v0)) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.step _v0 _v5 _v7))) (@Prod.snd.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step _v0 _v5 _v7)))))))),
(∀ {_v6 : (@Nat)},
(∀ {_v7 : (@Nat)},
(∀ (_v8 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v6 _v7)),
(∀ (_v9 : (@Nat)),
(∀ (_v10 : (@_v3 (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v6
  _v7 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v6 _v7 _v9 _v8)))),
(@Exists.{(0 + 1)} (@Nat) (fun (_v11 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v11 _v9) (@And (∀ (_v12 : (@Nat)),
(∀ (_v13 : (@LT.lt.{0} (@Nat) (@instLTNat) _v12 _v11)),
(@Not (@_v3 (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v6 _v7
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v6 _v7 _v12 _v8)))))) (@And (@Eq.{(0 + 1)}
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v6 _v7)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v6 _v7 _v11 _v8) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v6 _v7
  _v9 _v8)) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  _v1) _v6 _v7) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v1 _v6 _v7 _v11 (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v1) _v6 _v7 (@_v2 (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v6 _v7 _v8)) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v6 _v7 _v8) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v6 _v7 _v8))) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v1) _v6 _v7 (@_v2 (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v6 _v7 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v6 _v7
  _v9 _v8))) (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v6 _v7
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v6 _v7 _v9 _v8)) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v6 _v7 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v6 _v7
  _v9 _v8)))) (∀ (_v12 : (@Nat)),
(∀ (_v13 : (@LE.le.{0} (@Nat) (@instLENat) _v12 _v11)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v1) _v6 _v7)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v1 _v6 _v7 _v12 (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v1) _v6 _v7 (@_v2 (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v6 _v7 _v8)) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v6 _v7 _v8) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v6 _v7 _v8))) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v1) _v6 _v7 (@_v2 (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v6 _v7 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v6 _v7
  _v12 _v8))) (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v6 _v7
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v6 _v7 _v12 _v8)) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v6 _v7 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v0 _v6 _v7
  _v12 _v8))))))))))))))))))))))) := by
  exact @Cursor.Transport.first_changed_rows

-- Independent literal expected type for Cursor.mReady.
noncomputable def PartACanonical.Types.p0329 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(@Fin (@Cursor.stateCount _v0)))) := by
  exact @Cursor.mReady

-- Independent literal expected type for Cursor.machine.
noncomputable def PartACanonical.Types.p0330 :
(∀ (_v0 : (@Nat)),
(@Pnp3.Complexity.Uniform.V1.UniformTM)) := by
  exact @Cursor.machine

-- Independent literal expected type for Cursor.prefix_rows.
noncomputable def PartACanonical.Types.p0332 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@Cursor.stateCount _v0))),
(∀ (_v2 : (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Cursor.stateCount _v0) _v1) (@OfNat.ofNat.{0} (@Nat) (64 : Nat)
  (@instOfNatNat (64 : Nat))))),
(∀ (_v3 : (@Ne.{(0 + 1)} (@Nat) (@Fin.val (@Cursor.stateCount _v0) _v1) (@OfNat.ofNat.{0} (@Nat) (57 : Nat)
  (@instOfNatNat (57 : Nat))))),
(∀ (_v4 : (@Ne.{(0 + 1)} (@Nat) (@Fin.val (@Cursor.stateCount _v0) _v1) (@OfNat.ofNat.{0} (@Nat) (58 : Nat)
  (@instOfNatNat (58 : Nat))))),
(∀ (_v5 : (@Option.{0} (@Bool))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@Cursor.stateCount _v0)) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))) (@Cursor.rows _v0 _v1 _v5) (@Prod.mk.{0, 0} (@Fin (@Cursor.stateCount _v0))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.q _v0 (@Fin.val (@OfNat.ofNat.{0}
  (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) (@Prod.fst.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat
  (64 : Nat)))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Stream.rows (@Stream.q (@Fin.val
  (@Cursor.stateCount _v0) _v1)) _v5)))) (@Prod.snd.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 :
  Nat)))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Stream.rows (@Stream.q (@Fin.val
  (@Cursor.stateCount _v0) _v1)) _v5)))))))))) := by
  exact @Cursor.prefix_rows

-- Complete literal proposition for Cursor.prefix_rows; original proof reused.
theorem PartACanonical.Surface.m0206 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@Cursor.stateCount _v0))),
(∀ (_v2 : (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Cursor.stateCount _v0) _v1) (@OfNat.ofNat.{0} (@Nat) (64 : Nat)
  (@instOfNatNat (64 : Nat))))),
(∀ (_v3 : (@Ne.{(0 + 1)} (@Nat) (@Fin.val (@Cursor.stateCount _v0) _v1) (@OfNat.ofNat.{0} (@Nat) (57 : Nat)
  (@instOfNatNat (57 : Nat))))),
(∀ (_v4 : (@Ne.{(0 + 1)} (@Nat) (@Fin.val (@Cursor.stateCount _v0) _v1) (@OfNat.ofNat.{0} (@Nat) (58 : Nat)
  (@instOfNatNat (58 : Nat))))),
(∀ (_v5 : (@Option.{0} (@Bool))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@Cursor.stateCount _v0)) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))) (@Cursor.rows _v0 _v1 _v5) (@Prod.mk.{0, 0} (@Fin (@Cursor.stateCount _v0))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.q _v0 (@Fin.val (@OfNat.ofNat.{0}
  (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) (@Prod.fst.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat
  (64 : Nat)))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Stream.rows (@Stream.q (@Fin.val
  (@Cursor.stateCount _v0) _v1)) _v5)))) (@Prod.snd.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 :
  Nat)))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Stream.rows (@Stream.q (@Fin.val
  (@Cursor.stateCount _v0) _v1)) _v5)))))))))) := by
  exact @Cursor.prefix_rows

-- Independent literal expected type for Cursor.q.
noncomputable def PartACanonical.Types.p0333 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(@Fin (@Cursor.stateCount _v0)))) := by
  exact @Cursor.q

-- Independent literal expected type for Cursor.q.eq_1.
noncomputable def PartACanonical.Types.p0334 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(@Eq.{(0 + 1)} (@Fin (@Cursor.stateCount _v0)) (@Cursor.q _v0 _v1) (@Fin.mk (@Cursor.stateCount _v0) (@HMod.hMod.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHMod.{0} (@Nat) (@Nat.instMod)) _v1 (@Cursor.stateCount _v0)) (@Cursor.q._proof_2 _v0
  _v1))))) := by
  exact @Cursor.q.eq_1

-- Complete literal proposition for Cursor.q.eq_1; original proof reused.
theorem PartACanonical.Surface.m0207 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(@Eq.{(0 + 1)} (@Fin (@Cursor.stateCount _v0)) (@Cursor.q _v0 _v1) (@Fin.mk (@Cursor.stateCount _v0) (@HMod.hMod.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHMod.{0} (@Nat) (@Nat.instMod)) _v1 (@Cursor.stateCount _v0)) (@Cursor.q._proof_2 _v0
  _v1))))) := by
  exact @Cursor.q.eq_1

-- Independent literal expected type for Cursor.rReady.
noncomputable def PartACanonical.Types.p0335 :
(∀ (_v0 : (@Nat)),
(@Fin (@Cursor.stateCount _v0))) := by
  exact @Cursor.rReady

-- Independent literal expected type for Cursor.rReady.eq_1.
noncomputable def PartACanonical.Types.p0336 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@Fin (@Cursor.stateCount _v0)) (@Cursor.rReady _v0) (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (98 : Nat)
  (@instOfNatNat (98 : Nat)))))) := by
  exact @Cursor.rReady.eq_1

-- Complete literal proposition for Cursor.rReady.eq_1; original proof reused.
theorem PartACanonical.Surface.m0208 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@Fin (@Cursor.stateCount _v0)) (@Cursor.rReady _v0) (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (98 : Nat)
  (@instOfNatNat (98 : Nat)))))) := by
  exact @Cursor.rReady.eq_1

-- Independent literal expected type for Cursor.rawMachine.
noncomputable def PartACanonical.Types.p0337 :
(∀ (_v0 : (@Nat)),
(@Pnp3.Complexity.Uniform.V1.UniformTM)) := by
  exact @Cursor.rawMachine

-- Independent literal expected type for Cursor.rawMachine.eq_1.
noncomputable def PartACanonical.Types.p0338 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.UniformTM) (@Cursor.rawMachine _v0)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seq (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.prefixed) (@Cursor.machine
  _v0)))) := by
  exact @Cursor.rawMachine.eq_1

-- Complete literal proposition for Cursor.rawMachine.eq_1; original proof reused.
theorem PartACanonical.Surface.m0209 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.UniformTM) (@Cursor.rawMachine _v0)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seq (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.prefixed) (@Cursor.machine
  _v0)))) := by
  exact @Cursor.rawMachine.eq_1

-- Independent literal expected type for Cursor.raw_accepted_eof.
noncomputable def PartACanonical.Types.p0339 :
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
(@And (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v8) (@And (@Eq.{(0
  + 1)} (@Option.{0} (@Nat)) (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros? (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v3 _v4))
  (@Option.some.{0} (@Nat) _v8)) (∀ (_v9 : (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat)
  (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v8)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v9))) _v6)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v9))) _v6)))))),
(@Exists.{(0 + 1)} (@Nat) (fun (_v10 : (@Nat)) =>
(@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v2) _v8) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v11))) _v6))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat
  (3 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)))) (fun (_v11 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v2) _v8) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v11))) _v6))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat
  (3 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v10 (@Cursor.Target.deadline _v0
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2))) (@And (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Cursor.Target.M _v0
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v12))) _v6)) _v8)) (@And (@Eq.{(0 + 1)} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v3 _v4) (@Cursor.Target.M _v0
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v12))) _v6)) _v8)) (@Bool.false)) (let _v12 : (∀ (_v12 : (@Nat)),
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v12))) _v6))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v8) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat)))) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v12))) _v6))));
(let _v13 : (∀ (_v13 : (@Nat)),
(@Option.{0} (@Bool))) := (@Stream.Target.image _v12 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 _v2) _v8 (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v13))) _v6)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v8)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v13))) _v6))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v13))) _v6))) (@Bool.false));
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.rawMachine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Cursor.rawMachine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v10 (@Pnp3.Complexity.Uniform.V1.initialConfig (@Cursor.rawMachine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.prefixed)
  (@Cursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Cursor.mReady _v0 (@Fin.mk (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@of_decide_eq_true (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Nat.decLt
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 :
  Nat)))) (@id.{0} (@Eq.{(0 + 1)} (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Nat.decLt
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 :
  Nat))))) (@Bool.true)) (@Eq.refl.{(0 + 1)} (@Bool) (@Bool.true)))))) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v14))) _v6))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat
  (3 : Nat)))) _v11) (fun (_v14 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@_v13 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) _v14))))))))))))))))))))))))))))))) := by
  exact @Cursor.raw_accepted_eof

-- Complete literal proposition for Cursor.raw_accepted_eof; original proof reused.
theorem PartACanonical.Surface.m0210 :
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
(@And (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v8) (@And (@Eq.{(0
  + 1)} (@Option.{0} (@Nat)) (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros? (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v3 _v4))
  (@Option.some.{0} (@Nat) _v8)) (∀ (_v9 : (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat)
  (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v8)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v9))) _v6)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v9))) _v6)))))),
(@Exists.{(0 + 1)} (@Nat) (fun (_v10 : (@Nat)) =>
(@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v2) _v8) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v11))) _v6))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat
  (3 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)))) (fun (_v11 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v2) _v8) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v11))) _v6))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat
  (3 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v10 (@Cursor.Target.deadline _v0
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2))) (@And (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Cursor.Target.M _v0
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v12))) _v6)) _v8)) (@And (@Eq.{(0 + 1)} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v3 _v4) (@Cursor.Target.M _v0
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v12))) _v6)) _v8)) (@Bool.false)) (let _v12 : (∀ (_v12 : (@Nat)),
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v12))) _v6))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v8) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat)))) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v12))) _v6))));
(let _v13 : (∀ (_v13 : (@Nat)),
(@Option.{0} (@Bool))) := (@Stream.Target.image _v12 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 _v2) _v8 (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v13))) _v6)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v8)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v13))) _v6))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v13))) _v6))) (@Bool.false));
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.rawMachine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Cursor.rawMachine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v10 (@Pnp3.Complexity.Uniform.V1.initialConfig (@Cursor.rawMachine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.prefixed)
  (@Cursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Cursor.mReady _v0 (@Fin.mk (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@of_decide_eq_true (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Nat.decLt
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 :
  Nat)))) (@id.{0} (@Eq.{(0 + 1)} (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Nat.decLt
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 :
  Nat))))) (@Bool.true)) (@Eq.refl.{(0 + 1)} (@Bool) (@Bool.true)))))) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v14))) _v6))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat
  (3 : Nat)))) _v11) (fun (_v14 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@_v13 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) _v14))))))))))))))))))))))))))))))) := by
  exact @Cursor.raw_accepted_eof

-- Independent literal expected type for Cursor.raw_eof.
noncomputable def PartACanonical.Types.p0340 :
(∀ (_v0 : (@Nat)),
(@Cursor.Boundary.EOF _v0)) := by
  exact @Cursor.raw_eof

-- Complete literal proposition for Cursor.raw_eof; original proof reused.
theorem PartACanonical.Surface.m0211 :
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
(∀ (_v13 : (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 _v2) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 :
  Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))) _v9)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v13))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v13 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v13))) _v5)))))),
(@Exists.{(0 + 1)} (@Nat) (fun (_v14 : (@Nat)) =>
(@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v2) _v9) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v15))) _v5))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat
  (3 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)))) (fun (_v15 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v2) _v9) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v15))) _v5))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat
  (3 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v14 (@Cursor.Target.deadline _v0
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2))) (@And (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Cursor.Target.M _v0
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v16))) _v5)) _v9)) (@And (@Eq.{(0 + 1)} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v3 _v4) (@Cursor.Target.M _v0
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v16))) _v5)) _v9)) (@Bool.false)) (let _v16 : (∀ (_v16 : (@Nat)),
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
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.rawMachine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
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
  _v2)) (@Cursor.mReady _v0 (@Fin.mk (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@Cursor.Boundary.EOF._proof_1))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v9)
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v18))) _v5))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat
  (3 : Nat)))) _v15) (fun (_v18 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@_v17 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) _v18)))))))))))))))))))))))))))))))) := by
  exact @Cursor.raw_eof

-- Independent literal expected type for Cursor.raw_first.
noncomputable def PartACanonical.Types.p0341 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v2)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))))),
(∀ (_v7 : (@Or (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) _v6)
  (@OfNat.ofNat.{0} (@Nat) (57 : Nat) (@instOfNatNat (57 : Nat)))) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0}
  (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) _v6) (@OfNat.ofNat.{0} (@Nat) (58 : Nat) (@instOfNatNat (58 : Nat)))))),
(∀ (_v8 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))),
(∀ (_v9 : (∀ (_v9 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  _v1 _v2) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2))))),
(@Option.{0} (@Bool)))),
(∀ (_v10 : (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Stream.rawMachine)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Stream.rawMachine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v5 (@Pnp3.Complexity.Uniform.V1.initialConfig (@Stream.rawMachine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.prefixed)
  (@Stream.machine) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Stream.machine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v6 _v8 _v9)))),
(@Exists.{(0 + 1)} (@Nat) (fun (_v11 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v11 _v5) (@And (∀ (_v12 : (@Nat)),
(∀ (_v13 : (@LT.lt.{0} (@Nat) (@instLTNat) _v12 _v11)),
(@And (@Ne.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Stream.rawMachine))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Stream.rawMachine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Stream.rawMachine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v12 (@Pnp3.Complexity.Uniform.V1.initialConfig (@Stream.rawMachine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4))))) (@OfNat.ofNat.{0} (@Nat) (313 : Nat)
  (@instOfNatNat (313 : Nat)))) (@Ne.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Stream.rawMachine)) (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Stream.rawMachine)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Stream.rawMachine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v12 (@Pnp3.Complexity.Uniform.V1.initialConfig (@Stream.rawMachine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4))))) (@OfNat.ofNat.{0} (@Nat) (314 : Nat)
  (@instOfNatNat (314 : Nat))))))) (@And (∀ (_v12 : (@Nat)),
(∀ (_v13 : (@LT.lt.{0} (@Nat) (@instLTNat) _v12 _v11)),
(@And (@Ne.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.rawMachine _v0))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.rawMachine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Cursor.rawMachine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v12 (@Pnp3.Complexity.Uniform.V1.initialConfig (@Cursor.rawMachine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4))))) (@OfNat.ofNat.{0} (@Nat) (313 : Nat)
  (@instOfNatNat (313 : Nat)))) (@Ne.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Cursor.rawMachine _v0)) (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Cursor.rawMachine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Cursor.rawMachine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v12 (@Pnp3.Complexity.Uniform.V1.initialConfig (@Cursor.rawMachine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4))))) (@OfNat.ofNat.{0} (@Nat) (314 : Nat)
  (@instOfNatNat (314 : Nat))))))) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.rawMachine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
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
  _v2)) (@Cursor.q _v0 (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) _v6)) _v8
  _v9))))))))))))))))))) := by
  exact @Cursor.raw_first

-- Complete literal proposition for Cursor.raw_first; original proof reused.
theorem PartACanonical.Surface.m0212 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v2)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Fin (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))))),
(∀ (_v7 : (@Or (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) _v6)
  (@OfNat.ofNat.{0} (@Nat) (57 : Nat) (@instOfNatNat (57 : Nat)))) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0}
  (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) _v6) (@OfNat.ofNat.{0} (@Nat) (58 : Nat) (@instOfNatNat (58 : Nat)))))),
(∀ (_v8 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))),
(∀ (_v9 : (∀ (_v9 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  _v1 _v2) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2))))),
(@Option.{0} (@Bool)))),
(∀ (_v10 : (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Stream.rawMachine)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Stream.rawMachine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v5 (@Pnp3.Complexity.Uniform.V1.initialConfig (@Stream.rawMachine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.prefixed)
  (@Stream.machine) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Stream.machine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v6 _v8 _v9)))),
(@Exists.{(0 + 1)} (@Nat) (fun (_v11 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v11 _v5) (@And (∀ (_v12 : (@Nat)),
(∀ (_v13 : (@LT.lt.{0} (@Nat) (@instLTNat) _v12 _v11)),
(@And (@Ne.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Stream.rawMachine))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Stream.rawMachine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Stream.rawMachine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v12 (@Pnp3.Complexity.Uniform.V1.initialConfig (@Stream.rawMachine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4))))) (@OfNat.ofNat.{0} (@Nat) (313 : Nat)
  (@instOfNatNat (313 : Nat)))) (@Ne.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Stream.rawMachine)) (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Stream.rawMachine)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Stream.rawMachine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v12 (@Pnp3.Complexity.Uniform.V1.initialConfig (@Stream.rawMachine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4))))) (@OfNat.ofNat.{0} (@Nat) (314 : Nat)
  (@instOfNatNat (314 : Nat))))))) (@And (∀ (_v12 : (@Nat)),
(∀ (_v13 : (@LT.lt.{0} (@Nat) (@instLTNat) _v12 _v11)),
(@And (@Ne.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.rawMachine _v0))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.rawMachine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Cursor.rawMachine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v12 (@Pnp3.Complexity.Uniform.V1.initialConfig (@Cursor.rawMachine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4))))) (@OfNat.ofNat.{0} (@Nat) (313 : Nat)
  (@instOfNatNat (313 : Nat)))) (@Ne.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Cursor.rawMachine _v0)) (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Cursor.rawMachine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Cursor.rawMachine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v12 (@Pnp3.Complexity.Uniform.V1.initialConfig (@Cursor.rawMachine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4))))) (@OfNat.ofNat.{0} (@Nat) (314 : Nat)
  (@instOfNatNat (314 : Nat))))))) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.rawMachine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
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
  _v2)) (@Cursor.q _v0 (@Fin.val (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) _v6)) _v8
  _v9))))))))))))))))))) := by
  exact @Cursor.raw_first

-- Independent literal expected type for Cursor.raw_reject.
noncomputable def PartACanonical.Types.p0342 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))),
(∀ (_v6 : (∀ (_v6 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))),
(@Option.{0} (@Bool)))),
(∀ (_v7 : (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Stream.rawMachine)) _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Stream.rawMachine) _v1 _v2 _v4
  (@Pnp3.Complexity.Uniform.V1.initialConfig (@Stream.rawMachine) _v1 _v2 _v3))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.prefixed)
  (@Stream.machine) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Stream.machine)) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@Stream.machine)) _v5 _v6)))),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.rawMachine
  _v0)) _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Cursor.rawMachine _v0) _v1 _v2 _v4
  (@Pnp3.Complexity.Uniform.V1.initialConfig (@Cursor.rawMachine _v0) _v1 _v2 _v3))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.prefixed)
  (@Cursor.machine _v0) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Cursor.machine _v0)) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@Cursor.machine _v0)) _v5 _v6))))))))))) := by
  exact @Cursor.raw_reject

-- Complete literal proposition for Cursor.raw_reject; original proof reused.
theorem PartACanonical.Surface.m0213 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))),
(∀ (_v6 : (∀ (_v6 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))),
(@Option.{0} (@Bool)))),
(∀ (_v7 : (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Stream.rawMachine)) _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Stream.rawMachine) _v1 _v2 _v4
  (@Pnp3.Complexity.Uniform.V1.initialConfig (@Stream.rawMachine) _v1 _v2 _v3))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.prefixed)
  (@Stream.machine) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Stream.machine)) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@Stream.machine)) _v5 _v6)))),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.rawMachine
  _v0)) _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Cursor.rawMachine _v0) _v1 _v2 _v4
  (@Pnp3.Complexity.Uniform.V1.initialConfig (@Cursor.rawMachine _v0) _v1 _v2 _v3))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.prefixed)
  (@Cursor.machine _v0) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Cursor.machine _v0)) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@Cursor.machine _v0)) _v5 _v6))))))))))) := by
  exact @Cursor.raw_reject

-- Independent literal expected type for Cursor.raw_tail_blank.
noncomputable def PartACanonical.Types.p0343 :
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
(∀ (_v8 : (@LE.le.{0} (@Nat) (@instLENat) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v3)
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v0 _v1) _v2) _v3) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))))
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(let _v9 : (∀ (_v9 : (@Nat)),
(@Option.{0} (@Bool))) := (@Body.extend (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1)) (@Body.installedTape (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1)) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.countdownTape _v0 _v1
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1)) _v4 _v5 _v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v3) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1) _v2)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v3));
(let _v10 : (∀ (_v10 : (@Nat)),
(@Option.{0} (@Bool))) := (@Stream.Target.image _v9 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 _v1) _v2 _v3 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v2)) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v3) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v3)
  (@Bool.false));
(@And (∀ (_v11 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  _v0 _v1))))),
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1))) _v11))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1))) _v11)) (@Option.none.{0} (@Bool))))) (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat)
  (@instOfNatNat (5 : Nat))) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1) (@Min.min.{0} (@Nat)
  (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 :
  Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))) _v2)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v3))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1))))) _v3) (@OfNat.ofNat.{0}
  (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1)))))))))))))))) := by
  exact @Cursor.raw_tail_blank

-- Complete literal proposition for Cursor.raw_tail_blank; original proof reused.
theorem PartACanonical.Surface.m0214 :
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
(∀ (_v8 : (@LE.le.{0} (@Nat) (@instLENat) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v3)
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v0 _v1) _v2) _v3) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))))
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(let _v9 : (∀ (_v9 : (@Nat)),
(@Option.{0} (@Bool))) := (@Body.extend (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1)) (@Body.installedTape (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1)) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.countdownTape _v0 _v1
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1)) _v4 _v5 _v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v3) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1) _v2)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v3));
(let _v10 : (∀ (_v10 : (@Nat)),
(@Option.{0} (@Bool))) := (@Stream.Target.image _v9 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 _v1) _v2 _v3 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v2)) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v3) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v3)
  (@Bool.false));
(@And (∀ (_v11 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  _v0 _v1))))),
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1))) _v11))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1))) _v11)) (@Option.none.{0} (@Bool))))) (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat)
  (@instOfNatNat (5 : Nat))) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1) (@Min.min.{0} (@Nat)
  (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 :
  Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))) _v2)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v3))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1))))) _v3) (@OfNat.ofNat.{0}
  (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1)))))))))))))))) := by
  exact @Cursor.raw_tail_blank

-- Independent literal expected type for Cursor.rows.
noncomputable def PartACanonical.Types.p0344 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@Cursor.stateCount _v0))),
(∀ (_v2 : (@Option.{0} (@Bool))),
(@Prod.{0, 0} (@Fin (@Cursor.stateCount _v0)) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)))))) := by
  exact @Cursor.rows

-- Independent literal expected type for Cursor.stateCount.
noncomputable def PartACanonical.Types.p0346 :
(∀ (_v0 : (@Nat)),
(@Nat)) := by
  exact @Cursor.stateCount

-- Independent literal expected type for FullBodyClosure.Native.
noncomputable def PartACanonical.Types.p0347 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Config (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v0
  _v1)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Config (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v0
  _v1)),
(Sort 0)))))) := by
  exact @FullBodyClosure.Native

-- Independent literal expected type for FullBodyClosure.full_body.
noncomputable def PartACanonical.Types.p0348 :
(@SerializedBody.Target.Body) := by
  exact @FullBodyClosure.full_body

-- Complete literal proposition for FullBodyClosure.full_body; original proof reused.
theorem PartACanonical.Surface.m0216 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Nat)),
(∀ (_v8 : (@Nat)),
(∀ (_v9 : (∀ (_v9 : (@Fin _v1)),
(@Bool))),
(∀ (_v10 : (∀ (_v10 : (@Fin _v3)),
(@Bool))),
(∀ (_v11 : (∀ (_v11 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v12 : (@LE.le.{0} (@Nat) (@instLENat) _v4 _v1)),
(∀ (_v13 : (@LE.le.{0} (@Nat) (@instLENat) _v1 _v0)),
(∀ (_v14 : (@LE.le.{0} (@Nat) (@instLENat) _v5 _v4)),
(∀ (_v15 : (@LE.le.{0} (@Nat) (@instLENat) _v6 _v4)),
(∀ (_v16 : (@LE.le.{0} (@Nat) (@instLENat) (@Pnp4.Frontier.ContractExpansion.bitLength _v3) _v4)),
(∀ (_v17 : (@LE.le.{0} (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v1 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) _v7 _v1)) _v4)),
(let _v18 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation _v0);
(let _v19 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat))));
(let _v20 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v19 _v3) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat))));
(let _v21 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v0);
(∀ (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v8)),
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v20 _v8) _v21)),
(∀ (_v24 : (∀ (_v24 : (@Nat)),
(∀ (_v25 : (@LE.le.{0} (@Nat) (@instLENat) _v7 _v24)),
(∀ (_v26 : (@LT.lt.{0} (@Nat) (@instLTNat) _v24 _v1)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v11 _v24) (@Option.some.{0} (@Bool) (@_v9 (@Fin.mk _v1 _v24 _v26)))))))),
(∀ (_v25 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v11 _v1) (@Option.none.{0} (@Bool)))),
(∀ (_v26 : (∀ (_v26 : (@Nat)),
(∀ (_v27 : (@LT.lt.{0} (@Nat) (@instLTNat) _v1 _v26)),
(∀ (_v28 : (@LT.lt.{0} (@Nat) (@instLTNat) _v26 _v19)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v11 _v26) (@Option.some.{0} (@Bool) (@Bool.false))))))),
(∀ (_v27 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v11 _v19) (@Option.none.{0} (@Bool)))),
(∀ (_v28 : (∀ (_v28 : (@Fin _v3)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v11 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v20 (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Fin.val _v3 _v28))) (@Option.some.{0} (@Bool) (@_v10 _v28))))),
(∀ (_v29 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v11 _v20) (@Option.none.{0} (@Bool)))),
(∀ (_v30 : (∀ (_v30 : (@Nat)),
(∀ (_v31 : (@LT.lt.{0} (@Nat) (@instLTNat) _v20 _v30)),
(∀ (_v32 : (@LE.le.{0} (@Nat) (@instLENat) _v30 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v20 _v8))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v11 _v30) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v31 : (∀ (_v31 : (@Nat)),
(∀ (_v32 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v20 _v8) _v31)),
(∀ (_v33 : (@LT.lt.{0} (@Nat) (@instLTNat) _v31 _v21)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v11 _v31) (@Option.none.{0} (@Bool))))))),
(∀ (_v32 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v11 _v21) (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v33 : (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter _v21 _v4 _v3 (@OfNat.ofNat.{0} (@Nat) (12 : Nat)
  (@instOfNatNat (12 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v18))),
(∀ (_v34 : (@LT.lt.{0} (@Nat) (@instLTNat) _v20 (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v18))),
(let _v35 : (@List.{0} (@Bool)) := (@SerializedBody.window _v1 _v9 _v7 _v6);
(let _v36 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v0 _v18) := (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v0 _v18 (@SerializedBody.entry
  (@SerializedBody.sourceMode _v1 _v9 _v7)) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v18) _v20 _v34) (fun
  (_v36 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v18))) =>
(@SerializedBody.prepared _v11 _v1 _v7 _v21 _v4 _v3 _v5 _v6 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v18)
  _v36))));
(let _v37 : (@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool)))) := (@Bind.bind.{0, 0}
  (@Option.{0}) (@Monad.toBind.{0, 0} (@Option.{0}) (@instMonadOption.{0})) (@Prod.{0, 0} (@Pnp3.Models.Circuit _v3)
  (@List.{0} (@Bool))) (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool)))
  (@Pnp4.Frontier.ContractExpansion.decodeCircuitFull _v3 (@Pnp4.Frontier.ContractExpansion.bitLength _v3) _v35) (fun
  (_v37 : (@Prod.{0, 0} (@Pnp3.Models.Circuit _v3) (@List.{0} (@Bool)))) =>
(@SerializedBody.Target.Body.match_1.{(0 + 1)} _v3 (fun (_v38 : (@Prod.{0, 0} (@Pnp3.Models.Circuit _v3) (@List.{0}
  (@Bool)))) =>
(@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool))))) _v37 (fun (_v38 : (@Pnp3.Models.Circuit
  _v3)) =>
(fun (_v39 : (@List.{0} (@Bool))) =>
(@ite.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool)))) (@LE.le.{0} (@Nat)
  (@instLENat) (@Pnp3.Models.Circuit.size _v3 _v38) _v5) (@Nat.decLe (@Pnp3.Models.Circuit.size _v3 _v38) _v5)
  (@Option.some.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool))) (@Prod.mk.{0, 0} (@Prod.{0, 0} (@Nat)
  (@Bool)) (@List.{0} (@Bool)) (@Prod.mk.{0, 0} (@Nat) (@Bool) (@Pnp3.Models.Circuit.size _v3 _v38)
  (@Pnp3.Models.Circuit.eval _v3 _v38 _v10)) _v39)) (@Option.none.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool))
  (@List.{0} (@Bool))))))))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v38 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v38 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (1073741824 : Nat) (@instOfNatNat (1073741824 : Nat))) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))) (@And (∀ (_v39 : (@Nat)),
(∀ (_v40 : (@LE.le.{0} (@Nat) (@instLENat) _v39 _v38)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))
  _v0 _v18 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v18 _v39 _v36))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@SerializedBody.machine))))) (@And (∀ (_v39 : (@Nat)),
(∀ (_v40 : (@LT.lt.{0} (@Nat) (@instLTNat) _v39 _v38)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))
  _v0 _v18 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v18 _v39 _v36))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@SerializedBody.machine))) (@And (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v0 _v18
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v18 _v39 _v36)) (@SerializedBody.done
  (@Bool.false))) (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))
  _v0 _v18 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v18 _v39 _v36)) (@SerializedBody.done
  (@Bool.true))))))) (@SerializedBody.Target.Body.match_3.{(0 + 1)} (fun (_v39 : (@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0}
  (@Nat) (@Bool)) (@List.{0} (@Bool))))) =>
(Sort 0)) _v37 (fun (_v39 : (@Unit)) =>
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v0 _v18) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v18 _v38
  _v36) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v0 _v18 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@SerializedBody.machine)) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v18) _v20 _v34) (fun (_v40 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v0 _v18))) =>
(@SerializedBody.image _v11 _v21 _v4 _v3 _v5 _v6 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v1 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) _v7 _v1)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 :
  Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v18) _v40)))))) (fun (_v39 : (@Nat)) =>
(fun (_v40 : (@Bool)) =>
(fun (_v41 : (@List.{0} (@Bool))) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v42 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v42 _v6) (@And (@Eq.{(0 + 1)} (@List.{0} (@Bool)) _v41 (@List.drop.{0} (@Bool)
  _v42 _v35)) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v0 _v18) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v18 _v38
  _v36) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v0 _v18 (@SerializedBody.done _v40) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v0
  _v18) _v20 _v34) (fun (_v43 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v18))) =>
(@SerializedBody.image _v11 _v21 _v4 _v3 _v5 _v6 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v1 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) _v7 _v1)) _v39 _v42 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v6 _v42) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v18) _v43)))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @FullBodyClosure.full_body

-- Independent literal expected type for FullBodyClosure.full_body_mirror.
noncomputable def PartACanonical.Types.p0349 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Nat)),
(∀ (_v8 : (@Nat)),
(∀ (_v9 : (∀ (_v9 : (@Fin _v1)),
(@Bool))),
(∀ (_v10 : (∀ (_v10 : (@Fin _v3)),
(@Bool))),
(∀ (_v11 : (∀ (_v11 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v12 : (@LE.le.{0} (@Nat) (@instLENat) _v4 _v1)),
(∀ (_v13 : (@LE.le.{0} (@Nat) (@instLENat) _v1 _v0)),
(∀ (_v14 : (@LE.le.{0} (@Nat) (@instLENat) _v5 _v4)),
(∀ (_v15 : (@LE.le.{0} (@Nat) (@instLENat) _v6 _v4)),
(∀ (_v16 : (@LE.le.{0} (@Nat) (@instLENat) (@Pnp4.Frontier.ContractExpansion.bitLength _v3) _v4)),
(∀ (_v17 : (@LE.le.{0} (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v1 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) _v7 _v1)) _v4)),
(let _v18 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation _v0);
(let _v19 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat))));
(let _v20 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v19 _v3) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat))));
(let _v21 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v0);
(∀ (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v8)),
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v20 _v8) _v21)),
(∀ (_v24 : (∀ (_v24 : (@Nat)),
(∀ (_v25 : (@LE.le.{0} (@Nat) (@instLENat) _v7 _v24)),
(∀ (_v26 : (@LT.lt.{0} (@Nat) (@instLTNat) _v24 _v1)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v11 _v24) (@Option.some.{0} (@Bool) (@_v9 (@Fin.mk _v1 _v24 _v26)))))))),
(∀ (_v25 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v11 _v1) (@Option.none.{0} (@Bool)))),
(∀ (_v26 : (∀ (_v26 : (@Nat)),
(∀ (_v27 : (@LT.lt.{0} (@Nat) (@instLTNat) _v1 _v26)),
(∀ (_v28 : (@LT.lt.{0} (@Nat) (@instLTNat) _v26 _v19)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v11 _v26) (@Option.some.{0} (@Bool) (@Bool.false))))))),
(∀ (_v27 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v11 _v19) (@Option.none.{0} (@Bool)))),
(∀ (_v28 : (∀ (_v28 : (@Fin _v3)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v11 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v20 (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Fin.val _v3 _v28))) (@Option.some.{0} (@Bool) (@_v10 _v28))))),
(∀ (_v29 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v11 _v20) (@Option.none.{0} (@Bool)))),
(∀ (_v30 : (∀ (_v30 : (@Nat)),
(∀ (_v31 : (@LT.lt.{0} (@Nat) (@instLTNat) _v20 _v30)),
(∀ (_v32 : (@LE.le.{0} (@Nat) (@instLENat) _v30 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v20 _v8))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v11 _v30) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v31 : (∀ (_v31 : (@Nat)),
(∀ (_v32 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v20 _v8) _v31)),
(∀ (_v33 : (@LT.lt.{0} (@Nat) (@instLTNat) _v31 _v21)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v11 _v31) (@Option.none.{0} (@Bool))))))),
(∀ (_v32 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v11 _v21) (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v33 : (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter _v21 _v4 _v3 (@OfNat.ofNat.{0} (@Nat) (12 : Nat)
  (@instOfNatNat (12 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v18))),
(∀ (_v34 : (@LT.lt.{0} (@Nat) (@instLTNat) _v20 (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v18))),
(let _v35 : (@List.{0} (@Bool)) := (@SerializedBody.window _v1 _v9 _v7 _v6);
(let _v36 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v0 _v18) := (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v0 _v18 (@SerializedBody.entry
  (@SerializedBody.sourceMode _v1 _v9 _v7)) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v18) _v20 _v34) (fun
  (_v36 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v18))) =>
(@SerializedBody.prepared _v11 _v1 _v7 _v21 _v4 _v3 _v5 _v6 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v18)
  _v36))));
(let _v37 : (@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool)))) := (@Bind.bind.{0, 0}
  (@Option.{0}) (@Monad.toBind.{0, 0} (@Option.{0}) (@instMonadOption.{0})) (@Prod.{0, 0} (@Pnp3.Models.Circuit _v3)
  (@List.{0} (@Bool))) (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool)))
  (@Pnp4.Frontier.ContractExpansion.decodeCircuitFull _v3 (@Pnp4.Frontier.ContractExpansion.bitLength _v3) _v35) (fun
  (_v37 : (@Prod.{0, 0} (@Pnp3.Models.Circuit _v3) (@List.{0} (@Bool)))) =>
(@FullBodyClosure.full_body_mirror.match_1.{(0 + 1)} _v3 (fun (_v38 : (@Prod.{0, 0} (@Pnp3.Models.Circuit _v3)
  (@List.{0} (@Bool)))) =>
(@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool))))) _v37 (fun (_v38 : (@Pnp3.Models.Circuit
  _v3)) =>
(fun (_v39 : (@List.{0} (@Bool))) =>
(@ite.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool)))) (@LE.le.{0} (@Nat)
  (@instLENat) (@Pnp3.Models.Circuit.size _v3 _v38) _v5) (@Nat.decLe (@Pnp3.Models.Circuit.size _v3 _v38) _v5)
  (@Option.some.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool))) (@Prod.mk.{0, 0} (@Prod.{0, 0} (@Nat)
  (@Bool)) (@List.{0} (@Bool)) (@Prod.mk.{0, 0} (@Nat) (@Bool) (@Pnp3.Models.Circuit.size _v3 _v38)
  (@Pnp3.Models.Circuit.eval _v3 _v38 _v10)) _v39)) (@Option.none.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool))
  (@List.{0} (@Bool))))))))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v38 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v38 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (1073741824 : Nat) (@instOfNatNat (1073741824 : Nat))) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))) (@And (∀ (_v39 : (@Nat)),
(∀ (_v40 : (@LE.le.{0} (@Nat) (@instLENat) _v39 _v38)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))
  _v0 _v18 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v18 _v39 _v36))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@SerializedBody.machine))))) (@And (∀ (_v39 : (@Nat)),
(∀ (_v40 : (@LT.lt.{0} (@Nat) (@instLTNat) _v39 _v38)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))
  _v0 _v18 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v18 _v39 _v36))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@SerializedBody.machine))) (@And (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v0 _v18
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v18 _v39 _v36)) (@SerializedBody.done
  (@Bool.false))) (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))
  _v0 _v18 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v18 _v39 _v36)) (@SerializedBody.done
  (@Bool.true))))))) (@FullBodyClosure.full_body_mirror.match_3.{(0 + 1)} (fun (_v39 : (@Option.{0} (@Prod.{0, 0}
  (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool))))) =>
(Sort 0)) _v37 (fun (_v39 : (@Unit)) =>
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v0 _v18) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v18 _v38
  _v36) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v0 _v18 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@SerializedBody.machine)) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v18) _v20 _v34) (fun (_v40 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v0 _v18))) =>
(@SerializedBody.image _v11 _v21 _v4 _v3 _v5 _v6 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v1 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) _v7 _v1)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 :
  Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v18) _v40)))))) (fun (_v39 : (@Nat)) =>
(fun (_v40 : (@Bool)) =>
(fun (_v41 : (@List.{0} (@Bool))) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v42 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v42 _v6) (@And (@Eq.{(0 + 1)} (@List.{0} (@Bool)) _v41 (@List.drop.{0} (@Bool)
  _v42 _v35)) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v0 _v18) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v18 _v38
  _v36) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v0 _v18 (@SerializedBody.done _v40) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v0
  _v18) _v20 _v34) (fun (_v43 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v18))) =>
(@SerializedBody.image _v11 _v21 _v4 _v3 _v5 _v6 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v1 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) _v7 _v1)) _v39 _v42 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v6 _v42) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v18) _v43)))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @FullBodyClosure.full_body_mirror

-- Complete literal proposition for FullBodyClosure.full_body_mirror; original proof reused.
theorem PartACanonical.Surface.m0217 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Nat)),
(∀ (_v8 : (@Nat)),
(∀ (_v9 : (∀ (_v9 : (@Fin _v1)),
(@Bool))),
(∀ (_v10 : (∀ (_v10 : (@Fin _v3)),
(@Bool))),
(∀ (_v11 : (∀ (_v11 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v12 : (@LE.le.{0} (@Nat) (@instLENat) _v4 _v1)),
(∀ (_v13 : (@LE.le.{0} (@Nat) (@instLENat) _v1 _v0)),
(∀ (_v14 : (@LE.le.{0} (@Nat) (@instLENat) _v5 _v4)),
(∀ (_v15 : (@LE.le.{0} (@Nat) (@instLENat) _v6 _v4)),
(∀ (_v16 : (@LE.le.{0} (@Nat) (@instLENat) (@Pnp4.Frontier.ContractExpansion.bitLength _v3) _v4)),
(∀ (_v17 : (@LE.le.{0} (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v1 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) _v7 _v1)) _v4)),
(let _v18 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation _v0);
(let _v19 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat))));
(let _v20 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v19 _v3) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat))));
(let _v21 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v0);
(∀ (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v8)),
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v20 _v8) _v21)),
(∀ (_v24 : (∀ (_v24 : (@Nat)),
(∀ (_v25 : (@LE.le.{0} (@Nat) (@instLENat) _v7 _v24)),
(∀ (_v26 : (@LT.lt.{0} (@Nat) (@instLTNat) _v24 _v1)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v11 _v24) (@Option.some.{0} (@Bool) (@_v9 (@Fin.mk _v1 _v24 _v26)))))))),
(∀ (_v25 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v11 _v1) (@Option.none.{0} (@Bool)))),
(∀ (_v26 : (∀ (_v26 : (@Nat)),
(∀ (_v27 : (@LT.lt.{0} (@Nat) (@instLTNat) _v1 _v26)),
(∀ (_v28 : (@LT.lt.{0} (@Nat) (@instLTNat) _v26 _v19)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v11 _v26) (@Option.some.{0} (@Bool) (@Bool.false))))))),
(∀ (_v27 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v11 _v19) (@Option.none.{0} (@Bool)))),
(∀ (_v28 : (∀ (_v28 : (@Fin _v3)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v11 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v20 (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Fin.val _v3 _v28))) (@Option.some.{0} (@Bool) (@_v10 _v28))))),
(∀ (_v29 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v11 _v20) (@Option.none.{0} (@Bool)))),
(∀ (_v30 : (∀ (_v30 : (@Nat)),
(∀ (_v31 : (@LT.lt.{0} (@Nat) (@instLTNat) _v20 _v30)),
(∀ (_v32 : (@LE.le.{0} (@Nat) (@instLENat) _v30 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v20 _v8))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v11 _v30) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v31 : (∀ (_v31 : (@Nat)),
(∀ (_v32 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v20 _v8) _v31)),
(∀ (_v33 : (@LT.lt.{0} (@Nat) (@instLTNat) _v31 _v21)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v11 _v31) (@Option.none.{0} (@Bool))))))),
(∀ (_v32 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v11 _v21) (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v33 : (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter _v21 _v4 _v3 (@OfNat.ofNat.{0} (@Nat) (12 : Nat)
  (@instOfNatNat (12 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v18))),
(∀ (_v34 : (@LT.lt.{0} (@Nat) (@instLTNat) _v20 (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v18))),
(let _v35 : (@List.{0} (@Bool)) := (@SerializedBody.window _v1 _v9 _v7 _v6);
(let _v36 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v0 _v18) := (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v0 _v18 (@SerializedBody.entry
  (@SerializedBody.sourceMode _v1 _v9 _v7)) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v18) _v20 _v34) (fun
  (_v36 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v18))) =>
(@SerializedBody.prepared _v11 _v1 _v7 _v21 _v4 _v3 _v5 _v6 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v18)
  _v36))));
(let _v37 : (@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool)))) := (@Bind.bind.{0, 0}
  (@Option.{0}) (@Monad.toBind.{0, 0} (@Option.{0}) (@instMonadOption.{0})) (@Prod.{0, 0} (@Pnp3.Models.Circuit _v3)
  (@List.{0} (@Bool))) (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool)))
  (@Pnp4.Frontier.ContractExpansion.decodeCircuitFull _v3 (@Pnp4.Frontier.ContractExpansion.bitLength _v3) _v35) (fun
  (_v37 : (@Prod.{0, 0} (@Pnp3.Models.Circuit _v3) (@List.{0} (@Bool)))) =>
(@FullBodyClosure.full_body_mirror.match_1.{(0 + 1)} _v3 (fun (_v38 : (@Prod.{0, 0} (@Pnp3.Models.Circuit _v3)
  (@List.{0} (@Bool)))) =>
(@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool))))) _v37 (fun (_v38 : (@Pnp3.Models.Circuit
  _v3)) =>
(fun (_v39 : (@List.{0} (@Bool))) =>
(@ite.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool)))) (@LE.le.{0} (@Nat)
  (@instLENat) (@Pnp3.Models.Circuit.size _v3 _v38) _v5) (@Nat.decLe (@Pnp3.Models.Circuit.size _v3 _v38) _v5)
  (@Option.some.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool))) (@Prod.mk.{0, 0} (@Prod.{0, 0} (@Nat)
  (@Bool)) (@List.{0} (@Bool)) (@Prod.mk.{0, 0} (@Nat) (@Bool) (@Pnp3.Models.Circuit.size _v3 _v38)
  (@Pnp3.Models.Circuit.eval _v3 _v38 _v10)) _v39)) (@Option.none.{0} (@Prod.{0, 0} (@Prod.{0, 0} (@Nat) (@Bool))
  (@List.{0} (@Bool))))))))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v38 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v38 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (1073741824 : Nat) (@instOfNatNat (1073741824 : Nat))) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))) (@And (∀ (_v39 : (@Nat)),
(∀ (_v40 : (@LE.le.{0} (@Nat) (@instLENat) _v39 _v38)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))
  _v0 _v18 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v18 _v39 _v36))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@SerializedBody.machine))))) (@And (∀ (_v39 : (@Nat)),
(∀ (_v40 : (@LT.lt.{0} (@Nat) (@instLTNat) _v39 _v38)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))
  _v0 _v18 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v18 _v39 _v36))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@SerializedBody.machine))) (@And (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v0 _v18
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v18 _v39 _v36)) (@SerializedBody.done
  (@Bool.false))) (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))
  _v0 _v18 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v18 _v39 _v36)) (@SerializedBody.done
  (@Bool.true))))))) (@FullBodyClosure.full_body_mirror.match_3.{(0 + 1)} (fun (_v39 : (@Option.{0} (@Prod.{0, 0}
  (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool))))) =>
(Sort 0)) _v37 (fun (_v39 : (@Unit)) =>
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v0 _v18) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v18 _v38
  _v36) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v0 _v18 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@SerializedBody.machine)) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v18) _v20 _v34) (fun (_v40 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v0 _v18))) =>
(@SerializedBody.image _v11 _v21 _v4 _v3 _v5 _v6 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v1 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) _v7 _v1)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 :
  Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v18) _v40)))))) (fun (_v39 : (@Nat)) =>
(fun (_v40 : (@Bool)) =>
(fun (_v41 : (@List.{0} (@Bool))) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v42 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v42 _v6) (@And (@Eq.{(0 + 1)} (@List.{0} (@Bool)) _v41 (@List.drop.{0} (@Bool)
  _v42 _v35)) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v0 _v18) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v18 _v38
  _v36) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v0 _v18 (@SerializedBody.done _v40) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v0
  _v18) _v20 _v34) (fun (_v43 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v18))) =>
(@SerializedBody.image _v11 _v21 _v4 _v3 _v5 _v6 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v1 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) _v7 _v1)) _v39 _v42 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v6 _v42) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v18) _v43)))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @FullBodyClosure.full_body_mirror

-- Independent literal expected type for FullBodyClosure.native_trans.
noncomputable def PartACanonical.Types.p0350 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ {_v3 : (@Nat)},
(∀ {_v4 : (@Pnp3.Complexity.Uniform.V1.Config (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v0
  _v1)},
(∀ {_v5 : (@Pnp3.Complexity.Uniform.V1.Config (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v0
  _v1)},
(∀ {_v6 : (@Pnp3.Complexity.Uniform.V1.Config (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v0
  _v1)},
(∀ (_v7 : (@FullBodyClosure.Native _v0 _v1 _v2 _v4 _v5)),
(∀ (_v8 : (@FullBodyClosure.Native _v0 _v1 _v3 _v5 _v6)),
(@FullBodyClosure.Native _v0 _v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2
  _v3) _v4 _v6)))))))))) := by
  exact @FullBodyClosure.native_trans

-- Complete literal proposition for FullBodyClosure.native_trans; original proof reused.
theorem PartACanonical.Surface.m0218 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ {_v3 : (@Nat)},
(∀ {_v4 : (@Pnp3.Complexity.Uniform.V1.Config (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v0
  _v1)},
(∀ {_v5 : (@Pnp3.Complexity.Uniform.V1.Config (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v0
  _v1)},
(∀ {_v6 : (@Pnp3.Complexity.Uniform.V1.Config (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v0
  _v1)},
(∀ (_v7 : (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v0 _v1) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v1 _v2
  _v4) _v5) (∀ (_v7 : (@Nat)),
(∀ (_v8 : (@LT.lt.{0} (@Nat) (@instLTNat) _v7 _v2)),
(@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v0 _v1
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v1 _v7 _v4)))))))),
(∀ (_v8 : (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v0 _v1) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v1 _v3
  _v5) _v6) (∀ (_v8 : (@Nat)),
(∀ (_v9 : (@LT.lt.{0} (@Nat) (@instLTNat) _v8 _v3)),
(@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v0 _v1
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v1 _v8 _v5)))))))),
(@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v0 _v1) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v1
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v3) _v4) _v6) (∀ (_v9 : (@Nat)),
(∀ (_v10 : (@LT.lt.{0} (@Nat) (@instLTNat) _v9 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v2 _v3))),
(@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v0 _v1
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v1 _v9 _v4)))))))))))))))) := by
  exact @FullBodyClosure.native_trans

-- Independent literal expected type for FullBodyClosure.native_trans_mirror.
noncomputable def PartACanonical.Types.p0351 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ {_v3 : (@Nat)},
(∀ {_v4 : (@Pnp3.Complexity.Uniform.V1.Config (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v0
  _v1)},
(∀ {_v5 : (@Pnp3.Complexity.Uniform.V1.Config (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v0
  _v1)},
(∀ {_v6 : (@Pnp3.Complexity.Uniform.V1.Config (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v0
  _v1)},
(∀ (_v7 : (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v0 _v1) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v1 _v2
  _v4) _v5) (∀ (_v7 : (@Nat)),
(∀ (_v8 : (@LT.lt.{0} (@Nat) (@instLTNat) _v7 _v2)),
(@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v0 _v1
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v1 _v7 _v4)))))))),
(∀ (_v8 : (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v0 _v1) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v1 _v3
  _v5) _v6) (∀ (_v8 : (@Nat)),
(∀ (_v9 : (@LT.lt.{0} (@Nat) (@instLTNat) _v8 _v3)),
(@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v0 _v1
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v1 _v8 _v5)))))))),
(@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v0 _v1) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v1
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v3) _v4) _v6) (∀ (_v9 : (@Nat)),
(∀ (_v10 : (@LT.lt.{0} (@Nat) (@instLTNat) _v9 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v2 _v3))),
(@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v0 _v1
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v1 _v9 _v4)))))))))))))))) := by
  exact @FullBodyClosure.native_trans_mirror

-- Complete literal proposition for FullBodyClosure.native_trans_mirror; original proof reused.
theorem PartACanonical.Surface.m0219 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ {_v3 : (@Nat)},
(∀ {_v4 : (@Pnp3.Complexity.Uniform.V1.Config (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v0
  _v1)},
(∀ {_v5 : (@Pnp3.Complexity.Uniform.V1.Config (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v0
  _v1)},
(∀ {_v6 : (@Pnp3.Complexity.Uniform.V1.Config (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v0
  _v1)},
(∀ (_v7 : (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v0 _v1) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v1 _v2
  _v4) _v5) (∀ (_v7 : (@Nat)),
(∀ (_v8 : (@LT.lt.{0} (@Nat) (@instLTNat) _v7 _v2)),
(@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v0 _v1
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v1 _v7 _v4)))))))),
(∀ (_v8 : (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v0 _v1) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v1 _v3
  _v5) _v6) (∀ (_v8 : (@Nat)),
(∀ (_v9 : (@LT.lt.{0} (@Nat) (@instLTNat) _v8 _v3)),
(@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v0 _v1
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v1 _v8 _v5)))))))),
(@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v0 _v1) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v1
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v3) _v4) _v6) (∀ (_v9 : (@Nat)),
(∀ (_v10 : (@LT.lt.{0} (@Nat) (@instLTNat) _v9 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v2 _v3))),
(@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v0 _v1
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v1 _v9 _v4)))))))))))))))) := by
  exact @FullBodyClosure.native_trans_mirror

-- Independent literal expected type for FullFinalClosure.Target.Clock.
noncomputable def PartACanonical.Types.p0352 :
(∀ (_v0 : (@Nat)),
(Sort 0)) := by
  exact @FullFinalClosure.Target.Clock

-- Independent literal expected type for FullFinalClosure.Target.Full.
noncomputable def PartACanonical.Types.p0353 :
(∀ (_v0 : (@Nat)),
(Sort 0)) := by
  exact @FullFinalClosure.Target.Full

-- Independent literal expected type for FullFinalClosure.Target.Raw.
noncomputable def PartACanonical.Types.p0354 :
(∀ (_v0 : (@Nat)),
(Sort 0)) := by
  exact @FullFinalClosure.Target.Raw

-- Independent literal expected type for FullFinalClosure.Target.Witnesses.
noncomputable def PartACanonical.Types.p0355 :
(∀ (_v0 : (@Nat)),
(Sort 0)) := by
  exact @FullFinalClosure.Target.Witnesses

-- Independent literal expected type for FullFinalClosure.allocation.
noncomputable def PartACanonical.Types.p0356 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(@Nat))) := by
  exact @FullFinalClosure.allocation

-- Independent literal expected type for FullFinalClosure.check_clock_full.
noncomputable def PartACanonical.Types.p0357 :
(∀ (_v0 : (@Nat)),
(@And (@LE.le.{0} (@Nat) (@instLENat) (@FullFinalClosure.allocation _v0 (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))) (@Pnp3.Complexity.Uniform.V1.polyClock (@FullFinalClosure.degree _v0) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))) (@And (∀ (_v1 : (@Nat)),
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
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0) _v1 _v2))))))))))))) := by
  exact @FullFinalClosure.check_clock_full

-- Complete literal proposition for FullFinalClosure.check_clock_full; original proof reused.
theorem PartACanonical.Surface.m0220 :
(∀ (_v0 : (@Nat)),
(@And (@LE.le.{0} (@Nat) (@instLENat) (@FullFinalClosure.allocation _v0 (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))) (@Pnp3.Complexity.Uniform.V1.polyClock (@FullFinalClosure.degree _v0) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))) (@And (∀ (_v1 : (@Nat)),
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
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0) _v1 _v2))))))))))))) := by
  exact @FullFinalClosure.check_clock_full

-- Independent literal expected type for FullFinalClosure.check_full_endpoint_full.
noncomputable def PartACanonical.Types.p0358 :
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
  exact @FullFinalClosure.check_full_endpoint_full

-- Complete literal proposition for FullFinalClosure.check_full_endpoint_full; original proof reused.
theorem PartACanonical.Surface.m0221 :
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
  (∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(@And (@Ne.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))))
  (@Option.some.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine
  _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@Prod.mk.{0, 0} (@Fin
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
  (4 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (0 : Nat))))))
  (@Exists.{(0 + 1)} (@Nat) (fun (_v3 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool)))) (fun (_v4 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool)))
  (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0)))
  (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))))) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v3 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) _v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))) (@FullFinalClosure.degree _v0)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))
  (@FullFinalClosure.degree _v0)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@And (@Eq.{(0 + 1)}
  (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))))) (@UniformClassBridgeClosure.Ordinary.trace (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))))) (@StandardTMBridgeClosure.compile (@FullFinalClosure.machine _v0)) _v3
  (@Turing.TM0.init.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))) (@StandardTMBridgeClosure.encode (@List.ofFn.{0} (@Bool) _v1 _v2))))
  (@Option.some.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool)))) _v4)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))))) (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) _v4) (@ite.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))))) (@Eq.{(0 + 1)} (@Bool) (@UniformClassBridgeClosure.Ordinary.Verifies.match_1.{(0 +
  1)} (fun (_v5 : (@Option.{0} (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))) =>
(@Bool)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.decodePair _v1 _v2) (fun (_v5 : (@Unit)) =>
(@Bool.false)) (fun (_v5 : (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair)) =>
(@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 (@Sigma.fst.{0, 0} (@Nat) (fun (_v6
  : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6)) (@Prod.fst.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6))) (@Sigma.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6))) _v5)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6)) (@Prod.snd.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6))) (@Sigma.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6)) (@Prod.fst.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6))) (@Sigma.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6)) (@Prod.snd.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6))) (@Sigma.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6))) _v5))))) (@Bool.true)) (@instDecidableEqBool
  (@UniformClassBridgeClosure.Ordinary.Verifies.match_1.{(0 + 1)} (fun (_v5 : (@Option.{0}
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))) =>
(@Bool)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.decodePair _v1 _v2) (fun (_v5 : (@Unit)) =>
(@Bool.false)) (fun (_v5 : (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair)) =>
(@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 (@Sigma.fst.{0, 0} (@Nat) (fun (_v6
  : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6)) (@Prod.fst.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6))) (@Sigma.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6))) _v5)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6)) (@Prod.snd.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6))) (@Sigma.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6)) (@Prod.fst.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6))) (@Sigma.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6)) (@Prod.snd.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6))) (@Sigma.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6))) _v5))))) (@Bool.true)) (@Option.some.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@FullFinalClosure.machine _v0)) (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0}
  (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat
  (4 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (0 : Nat)))))
  (@Option.some.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine
  _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@Prod.mk.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@FullFinalClosure.machine _v0))
  (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (0 : Nat))))))) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0}
  (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))))
  (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool)))))
  (@Turing.TM0.step.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))) (@StandardTMBridgeClosure.compile (@FullFinalClosure.machine _v0)) _v4)
  (@Option.none.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool)))))) (∀ (_v5 : (@Nat)),
(∀ (_v6 : (@LT.lt.{0} (@Nat) (@instLTNat) _v5 _v3)),
(∀ (_v7 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))))),
(∀ (_v8 : (@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))))) (@UniformClassBridgeClosure.Ordinary.trace
  (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0)))
  (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))))) (@StandardTMBridgeClosure.compile (@FullFinalClosure.machine _v0)) _v5
  (@Turing.TM0.init.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))) (@StandardTMBridgeClosure.encode (@List.ofFn.{0} (@Bool) _v1 _v2))))
  (@Option.some.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool)))) _v7))),
(@And (@Ne.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))))
  (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))) _v7) (@Option.some.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@FullFinalClosure.machine _v0)) (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0}
  (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat
  (4 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (0 : Nat)))))) (@Ne.{(0
  + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine
  _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0}
  (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))))
  (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) _v7)
  (@Option.some.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine
  _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@Prod.mk.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@FullFinalClosure.machine _v0))
  (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (0 : Nat)))))))))))))))))))))) (@Exists.{(0 + 1)}
  (@Pnp3.Complexity.Uniform.V1.WitnessRelation) (fun (_v1 : (@Pnp3.Complexity.Uniform.V1.WitnessRelation)) =>
(@Exists.{((0 + 1) + 1)} (Sort (0 + 1)) (fun (_v2 : (Sort (0 + 1))) =>
(@Exists.{(0 + 1)} (@Fintype.{0} _v2) (fun (_v3 : (@Fintype.{0} _v2)) =>
(@Exists.{(0 + 1)} (@Inhabited.{(0 + 1)} _v2) (fun (_v4 : (@Inhabited.{(0 + 1)} _v2)) =>
(@Exists.{(0 + 1)} (@Turing.TM0.Machine.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v2 _v4) (fun (_v5 :
  (@Turing.TM0.Machine.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v2 _v4)) =>
(@Exists.{(0 + 1)} _v2 (fun (_v6 : _v2) =>
(@Exists.{(0 + 1)} _v2 (fun (_v7 : _v2) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v8 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v9 : (@Nat)) =>
(@And (∀ (_v10 : (@Nat)),
(∀ (_v11 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v10)),
(@And (@Ne.{(0 + 1)} _v2 _v6 _v7) (@Exists.{(0 + 1)} (@Nat) (fun (_v12 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v2 (@instInhabitedProd.{0, 0}
  (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool)))) (fun (_v13 :
  (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v2 (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))))) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v12 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) _v10 _v8) _v8)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool)
  (@Option.{0} (@Bool))) _v2 (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))))) (@UniformClassBridgeClosure.Ordinary.trace _v2 _v4 _v5 _v12 (@Turing.TM0.init.{0,
  0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v2 _v4 (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool))
  (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) (@StandardTMBridgeClosure.encode (@List.ofFn.{0} (@Bool) _v10
  _v11)))) (@Option.some.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v2
  (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))))
  _v13)) (@And (@Eq.{(0 + 1)} _v2 (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v2
  (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) _v13)
  (@ite.{(0 + 1)} _v2 (@Eq.{(0 + 1)} (@Bool) (@UniformClassBridgeClosure.Ordinary.Verifies.match_1.{(0 + 1)} (fun (_v14 :
  (@Option.{0} (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))) =>
(@Bool)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.decodePair _v10 _v11) (fun (_v14 : (@Unit)) =>
(@Bool.false)) (fun (_v14 : (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair)) =>
(@_v1 (@Sigma.fst.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15)) (@Prod.fst.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15))) (@Sigma.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15))) _v14)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15)) (@Prod.snd.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15))) (@Sigma.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15))) _v14)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15)) (@Prod.fst.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15))) (@Sigma.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15))) _v14)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15)) (@Prod.snd.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15))) (@Sigma.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15))) _v14))))) (@Bool.true)) (@instDecidableEqBool
  (@UniformClassBridgeClosure.Ordinary.Verifies.match_1.{(0 + 1)} (fun (_v14 : (@Option.{0}
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))) =>
(@Bool)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.decodePair _v10 _v11) (fun (_v14 : (@Unit)) =>
(@Bool.false)) (fun (_v14 : (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair)) =>
(@_v1 (@Sigma.fst.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15)) (@Prod.fst.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15))) (@Sigma.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15))) _v14)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15)) (@Prod.snd.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15))) (@Sigma.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15))) _v14)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15)) (@Prod.fst.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15))) (@Sigma.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15))) _v14)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15)) (@Prod.snd.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15))) (@Sigma.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15))) _v14))))) (@Bool.true)) _v6 _v7)) (@And (@Eq.{(0 + 1)} (@Option.{0}
  (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v2 (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))))) (@Turing.TM0.step.{0, 0} (@Prod.{0, 0} (@Bool)
  (@Option.{0} (@Bool))) _v2 _v4 (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))) _v5 _v13) (@Option.none.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool)
  (@Option.{0} (@Bool))) _v2 (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool)))))) (∀ (_v14 : (@Nat)),
(∀ (_v15 : (@LT.lt.{0} (@Nat) (@instLTNat) _v14 _v12)),
(∀ (_v16 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v2 (@instInhabitedProd.{0, 0} (@Bool)
  (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))))),
(∀ (_v17 : (@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v2
  (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool)))))
  (@UniformClassBridgeClosure.Ordinary.trace _v2 _v4 _v5 _v14 (@Turing.TM0.init.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0}
  (@Bool))) _v2 _v4 (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))) (@StandardTMBridgeClosure.encode (@List.ofFn.{0} (@Bool) _v10 _v11))))
  (@Option.some.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v2 (@instInhabitedProd.{0, 0}
  (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool)))) _v16))),
(@And (@Ne.{(0 + 1)} _v2 (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v2
  (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) _v16)
  _v6) (@Ne.{(0 + 1)} _v2 (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v2
  (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) _v16)
  _v7))))))))))))))))) (∀ (_v10 : (@Nat)),
(∀ (_v11 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v10)),
(@Iff (@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.ContentPrefixExtensionLanguage
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v10 _v11) (@Bool.true)) (@Exists.{(0 + 1)} (@Nat) (fun (_v12 :
  (@Nat)) =>
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v12) (fun (_v13 : (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v12)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v12 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) _v10 _v9) _v9)) (@Eq.{(0 + 1)} (@Bool) (@_v1 _v10 _v12 _v11 _v13)
  (@Bool.true)))))))))))))))))))))))))))))))))))) := by
  exact @FullFinalClosure.check_full_endpoint_full

-- Independent literal expected type for FullFinalClosure.check_ordinary_uniformNP_full.
noncomputable def PartACanonical.Types.p0359 :
(∀ (_v0 : (@Nat)),
(@UniformClassBridgeClosure.Ordinary.UniformNP (@Pnp4.Frontier.ContractExpansion.ContentPrefixExtensionLanguage
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))))) := by
  exact @FullFinalClosure.check_ordinary_uniformNP_full

-- Complete literal proposition for FullFinalClosure.check_ordinary_uniformNP_full; original proof reused.
theorem PartACanonical.Surface.m0222 :
(∀ (_v0 : (@Nat)),
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.WitnessRelation) (fun (_v1 :
  (@Pnp3.Complexity.Uniform.V1.WitnessRelation)) =>
(@Exists.{((0 + 1) + 1)} (Sort (0 + 1)) (fun (_v2 : (Sort (0 + 1))) =>
(@Exists.{(0 + 1)} (@Fintype.{0} _v2) (fun (_v3 : (@Fintype.{0} _v2)) =>
(@Exists.{(0 + 1)} (@Inhabited.{(0 + 1)} _v2) (fun (_v4 : (@Inhabited.{(0 + 1)} _v2)) =>
(@Exists.{(0 + 1)} (@Turing.TM0.Machine.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v2 _v4) (fun (_v5 :
  (@Turing.TM0.Machine.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v2 _v4)) =>
(@Exists.{(0 + 1)} _v2 (fun (_v6 : _v2) =>
(@Exists.{(0 + 1)} _v2 (fun (_v7 : _v2) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v8 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v9 : (@Nat)) =>
(@And (∀ (_v10 : (@Nat)),
(∀ (_v11 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v10)),
(@And (@Ne.{(0 + 1)} _v2 _v6 _v7) (@Exists.{(0 + 1)} (@Nat) (fun (_v12 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v2 (@instInhabitedProd.{0, 0}
  (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool)))) (fun (_v13 :
  (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v2 (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))))) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v12 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) _v10 _v8) _v8)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool)
  (@Option.{0} (@Bool))) _v2 (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))))) (@UniformClassBridgeClosure.Ordinary.trace _v2 _v4 _v5 _v12 (@Turing.TM0.init.{0,
  0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v2 _v4 (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool))
  (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) (@StandardTMBridgeClosure.encode (@List.ofFn.{0} (@Bool) _v10
  _v11)))) (@Option.some.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v2
  (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))))
  _v13)) (@And (@Eq.{(0 + 1)} _v2 (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v2
  (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) _v13)
  (@ite.{(0 + 1)} _v2 (@Eq.{(0 + 1)} (@Bool) (@UniformClassBridgeClosure.Ordinary.Verifies.match_1.{(0 + 1)} (fun (_v14 :
  (@Option.{0} (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))) =>
(@Bool)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.decodePair _v10 _v11) (fun (_v14 : (@Unit)) =>
(@Bool.false)) (fun (_v14 : (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair)) =>
(@_v1 (@Sigma.fst.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15)) (@Prod.fst.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15))) (@Sigma.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15))) _v14)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15)) (@Prod.snd.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15))) (@Sigma.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15))) _v14)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15)) (@Prod.fst.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15))) (@Sigma.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15))) _v14)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15)) (@Prod.snd.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15))) (@Sigma.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15))) _v14))))) (@Bool.true)) (@instDecidableEqBool
  (@UniformClassBridgeClosure.Ordinary.Verifies.match_1.{(0 + 1)} (fun (_v14 : (@Option.{0}
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))) =>
(@Bool)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.decodePair _v10 _v11) (fun (_v14 : (@Unit)) =>
(@Bool.false)) (fun (_v14 : (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair)) =>
(@_v1 (@Sigma.fst.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15)) (@Prod.fst.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15))) (@Sigma.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15))) _v14)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15)) (@Prod.snd.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15))) (@Sigma.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15))) _v14)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15)) (@Prod.fst.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15))) (@Sigma.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15))) _v14)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15)) (@Prod.snd.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15))) (@Sigma.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15))) _v14))))) (@Bool.true)) _v6 _v7)) (@And (@Eq.{(0 + 1)} (@Option.{0}
  (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v2 (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))))) (@Turing.TM0.step.{0, 0} (@Prod.{0, 0} (@Bool)
  (@Option.{0} (@Bool))) _v2 _v4 (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))) _v5 _v13) (@Option.none.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool)
  (@Option.{0} (@Bool))) _v2 (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool)))))) (∀ (_v14 : (@Nat)),
(∀ (_v15 : (@LT.lt.{0} (@Nat) (@instLTNat) _v14 _v12)),
(∀ (_v16 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v2 (@instInhabitedProd.{0, 0} (@Bool)
  (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))))),
(∀ (_v17 : (@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v2
  (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool)))))
  (@UniformClassBridgeClosure.Ordinary.trace _v2 _v4 _v5 _v14 (@Turing.TM0.init.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0}
  (@Bool))) _v2 _v4 (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))) (@StandardTMBridgeClosure.encode (@List.ofFn.{0} (@Bool) _v10 _v11))))
  (@Option.some.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v2 (@instInhabitedProd.{0, 0}
  (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool)))) _v16))),
(@And (@Ne.{(0 + 1)} _v2 (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v2
  (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) _v16)
  _v6) (@Ne.{(0 + 1)} _v2 (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v2
  (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) _v16)
  _v7))))))))))))))))) (∀ (_v10 : (@Nat)),
(∀ (_v11 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v10)),
(@Iff (@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.ContentPrefixExtensionLanguage
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v10 _v11) (@Bool.true)) (@Exists.{(0 + 1)} (@Nat) (fun (_v12 :
  (@Nat)) =>
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v12) (fun (_v13 : (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v12)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v12 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) _v10 _v9) _v9)) (@Eq.{(0 + 1)} (@Bool) (@_v1 _v10 _v12 _v11 _v13)
  (@Bool.true)))))))))))))))))))))))))))))) := by
  exact @FullFinalClosure.check_ordinary_uniformNP_full

-- Independent literal expected type for FullFinalClosure.check_ordinary_verifier_full.
noncomputable def PartACanonical.Types.p0360 :
(∀ (_v0 : (@Nat)),
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
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0))) := by
  exact @FullFinalClosure.check_ordinary_verifier_full

-- Complete literal proposition for FullFinalClosure.check_ordinary_verifier_full; original proof reused.
theorem PartACanonical.Surface.m0223 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(@And (@Ne.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))))
  (@Option.some.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine
  _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@Prod.mk.{0, 0} (@Fin
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
  (4 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (0 : Nat))))))
  (@Exists.{(0 + 1)} (@Nat) (fun (_v3 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool)))) (fun (_v4 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool)))
  (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0)))
  (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))))) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v3 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) _v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))) (@FullFinalClosure.degree _v0)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))
  (@FullFinalClosure.degree _v0)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@And (@Eq.{(0 + 1)}
  (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))))) (@UniformClassBridgeClosure.Ordinary.trace (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))))) (@StandardTMBridgeClosure.compile (@FullFinalClosure.machine _v0)) _v3
  (@Turing.TM0.init.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))) (@StandardTMBridgeClosure.encode (@List.ofFn.{0} (@Bool) _v1 _v2))))
  (@Option.some.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool)))) _v4)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))))) (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) _v4) (@ite.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))))) (@Eq.{(0 + 1)} (@Bool) (@UniformClassBridgeClosure.Ordinary.Verifies.match_1.{(0 +
  1)} (fun (_v5 : (@Option.{0} (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))) =>
(@Bool)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.decodePair _v1 _v2) (fun (_v5 : (@Unit)) =>
(@Bool.false)) (fun (_v5 : (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair)) =>
(@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 (@Sigma.fst.{0, 0} (@Nat) (fun (_v6
  : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6)) (@Prod.fst.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6))) (@Sigma.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6))) _v5)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6)) (@Prod.snd.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6))) (@Sigma.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6)) (@Prod.fst.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6))) (@Sigma.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6)) (@Prod.snd.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6))) (@Sigma.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6))) _v5))))) (@Bool.true)) (@instDecidableEqBool
  (@UniformClassBridgeClosure.Ordinary.Verifies.match_1.{(0 + 1)} (fun (_v5 : (@Option.{0}
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))) =>
(@Bool)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.decodePair _v1 _v2) (fun (_v5 : (@Unit)) =>
(@Bool.false)) (fun (_v5 : (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair)) =>
(@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 (@Sigma.fst.{0, 0} (@Nat) (fun (_v6
  : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6)) (@Prod.fst.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6))) (@Sigma.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6))) _v5)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6)) (@Prod.snd.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6))) (@Sigma.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6)) (@Prod.fst.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6))) (@Sigma.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6)) (@Prod.snd.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6))) (@Sigma.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6))) _v5))))) (@Bool.true)) (@Option.some.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@FullFinalClosure.machine _v0)) (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0}
  (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat
  (4 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (0 : Nat)))))
  (@Option.some.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine
  _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@Prod.mk.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@FullFinalClosure.machine _v0))
  (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (0 : Nat))))))) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0}
  (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))))
  (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool)))))
  (@Turing.TM0.step.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))) (@StandardTMBridgeClosure.compile (@FullFinalClosure.machine _v0)) _v4)
  (@Option.none.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool)))))) (∀ (_v5 : (@Nat)),
(∀ (_v6 : (@LT.lt.{0} (@Nat) (@instLTNat) _v5 _v3)),
(∀ (_v7 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))))),
(∀ (_v8 : (@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))))) (@UniformClassBridgeClosure.Ordinary.trace
  (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0)))
  (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))))) (@StandardTMBridgeClosure.compile (@FullFinalClosure.machine _v0)) _v5
  (@Turing.TM0.init.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))) (@StandardTMBridgeClosure.encode (@List.ofFn.{0} (@Bool) _v1 _v2))))
  (@Option.some.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool)))) _v7))),
(@And (@Ne.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))))
  (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))) _v7) (@Option.some.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@FullFinalClosure.machine _v0)) (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0}
  (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat
  (4 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (0 : Nat)))))) (@Ne.{(0
  + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine
  _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0}
  (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))))
  (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) _v7)
  (@Option.some.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine
  _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@Prod.mk.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@FullFinalClosure.machine _v0))
  (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (0 : Nat))))))))))))))))))))))) := by
  exact @FullFinalClosure.check_ordinary_verifier_full

-- Independent literal expected type for FullFinalClosure.check_raw_full.
noncomputable def PartACanonical.Types.p0361 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
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
  _v24)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @FullFinalClosure.check_raw_full

-- Complete literal proposition for FullFinalClosure.check_raw_full; original proof reused.
theorem PartACanonical.Surface.m0224 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
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
  _v24)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @FullFinalClosure.check_raw_full

-- Independent literal expected type for FullFinalClosure.check_uniformNP_full.
noncomputable def PartACanonical.Types.p0362 :
(∀ (_v0 : (@Nat)),
(@Pnp3.Complexity.Uniform.V1.UniformNP (@Pnp4.Frontier.ContractExpansion.ContentPrefixExtensionLanguage
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))))) := by
  exact @FullFinalClosure.check_uniformNP_full

-- Complete literal proposition for FullFinalClosure.check_uniformNP_full; original proof reused.
theorem PartACanonical.Surface.m0225 :
(∀ (_v0 : (@Nat)),
(@Pnp3.Complexity.Uniform.V1.UniformNP (@Pnp4.Frontier.ContractExpansion.ContentPrefixExtensionLanguage
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))))) := by
  exact @FullFinalClosure.check_uniformNP_full

-- Independent literal expected type for FullFinalClosure.check_verifier_full.
noncomputable def PartACanonical.Types.p0363 :
(∀ (_v0 : (@Nat)),
(@Pnp3.Complexity.Uniform.V1.VerifiesRelation (@FullFinalClosure.machine _v0) (@FullFinalClosure.degree _v0)
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0))) := by
  exact @FullFinalClosure.check_verifier_full

-- Complete literal proposition for FullFinalClosure.check_verifier_full; original proof reused.
theorem PartACanonical.Surface.m0226 :
(∀ (_v0 : (@Nat)),
(@Pnp3.Complexity.Uniform.V1.VerifiesRelation (@FullFinalClosure.machine _v0) (@FullFinalClosure.degree _v0)
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0))) := by
  exact @FullFinalClosure.check_verifier_full

-- Independent literal expected type for FullFinalClosure.check_witnesses_full.
noncomputable def PartACanonical.Types.p0364 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
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
  (@Bool.true))))))))))) := by
  exact @FullFinalClosure.check_witnesses_full

-- Complete literal proposition for FullFinalClosure.check_witnesses_full; original proof reused.
theorem PartACanonical.Surface.m0227 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
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
  (@Bool.true))))))))))) := by
  exact @FullFinalClosure.check_witnesses_full

-- Independent literal expected type for FullFinalClosure.clock_full.
noncomputable def PartACanonical.Types.p0365 :
(∀ (_v0 : (@Nat)),
(@And (@LE.le.{0} (@Nat) (@instLENat) (@FullFinalClosure.allocation _v0 (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))) (@Pnp3.Complexity.Uniform.V1.polyClock (@FullFinalClosure.degree _v0) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))) (@And (∀ (_v1 : (@Nat)),
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
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0) _v1 _v2))))))))))))) := by
  exact @FullFinalClosure.clock_full

-- Complete literal proposition for FullFinalClosure.clock_full; original proof reused.
theorem PartACanonical.Surface.m0228 :
(∀ (_v0 : (@Nat)),
(@And (@LE.le.{0} (@Nat) (@instLENat) (@FullFinalClosure.allocation _v0 (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))) (@Pnp3.Complexity.Uniform.V1.polyClock (@FullFinalClosure.degree _v0) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))) (@And (∀ (_v1 : (@Nat)),
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
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0) _v1 _v2))))))))))))) := by
  exact @FullFinalClosure.clock_full

-- Independent literal expected type for FullFinalClosure.configA.
noncomputable def PartACanonical.Types.p0366 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@VirtualFinalClosure.machine _v0)) _v1 _v2)),
(@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))
  _v1 _v2))))) := by
  exact @FullFinalClosure.configA

-- Independent literal expected type for FullFinalClosure.configB.
noncomputable def PartACanonical.Types.p0367 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@NormalFinalClosure.machine2 _v0)) _v1 _v2)),
(@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))
  _v1 _v2))))) := by
  exact @FullFinalClosure.configB

-- Independent literal expected type for FullFinalClosure.count.
noncomputable def PartACanonical.Types.p0368 :
(∀ (_v0 : (@Nat)),
(@Nat)) := by
  exact @FullFinalClosure.count

-- Independent literal expected type for FullFinalClosure.degree.
noncomputable def PartACanonical.Types.p0369 :
(∀ (_v0 : (@Nat)),
(@Nat)) := by
  exact @FullFinalClosure.degree

-- Independent literal expected type for FullFinalClosure.dispatch.
noncomputable def PartACanonical.Types.p0370 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@VirtualFinalClosure.machine _v0)))),
(@Option.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))))) := by
  exact @FullFinalClosure.dispatch

-- Independent literal expected type for FullFinalClosure.entryA.
noncomputable def PartACanonical.Types.p0371 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@VirtualFinalClosure.machine _v0))))) := by
  exact @FullFinalClosure.entryA

-- Independent literal expected type for FullFinalClosure.entryB.
noncomputable def PartACanonical.Types.p0372 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2 _v0))))) := by
  exact @FullFinalClosure.entryB

-- Independent literal expected type for FullFinalClosure.left.
noncomputable def PartACanonical.Types.p0374 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@VirtualFinalClosure.machine _v0)))),
(@Fin (@FullFinalClosure.count _v0)))) := by
  exact @FullFinalClosure.left

-- Independent literal expected type for FullFinalClosure.normalBase.
noncomputable def PartACanonical.Types.p0376 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ {_v2 : (@Nat)},
(∀ {_v3 : (@Nat)},
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v2)),
(∀ (_v5 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v3)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Nat)),
(∀ (_v8 : (@Nat)),
(@Option.{0} (@Bool))))))))))) := by
  exact @FullFinalClosure.normalBase

-- Independent literal expected type for FullFinalClosure.ordinary_uniformNP_full.
noncomputable def PartACanonical.Types.p0377 :
(∀ (_v0 : (@Nat)),
(@UniformClassBridgeClosure.Ordinary.UniformNP (@Pnp4.Frontier.ContractExpansion.ContentPrefixExtensionLanguage
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))))) := by
  exact @FullFinalClosure.ordinary_uniformNP_full

-- Complete literal proposition for FullFinalClosure.ordinary_uniformNP_full; original proof reused.
theorem PartACanonical.Surface.m0230 :
(∀ (_v0 : (@Nat)),
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.WitnessRelation) (fun (_v1 :
  (@Pnp3.Complexity.Uniform.V1.WitnessRelation)) =>
(@Exists.{((0 + 1) + 1)} (Sort (0 + 1)) (fun (_v2 : (Sort (0 + 1))) =>
(@Exists.{(0 + 1)} (@Fintype.{0} _v2) (fun (_v3 : (@Fintype.{0} _v2)) =>
(@Exists.{(0 + 1)} (@Inhabited.{(0 + 1)} _v2) (fun (_v4 : (@Inhabited.{(0 + 1)} _v2)) =>
(@Exists.{(0 + 1)} (@Turing.TM0.Machine.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v2 _v4) (fun (_v5 :
  (@Turing.TM0.Machine.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v2 _v4)) =>
(@Exists.{(0 + 1)} _v2 (fun (_v6 : _v2) =>
(@Exists.{(0 + 1)} _v2 (fun (_v7 : _v2) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v8 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v9 : (@Nat)) =>
(@And (∀ (_v10 : (@Nat)),
(∀ (_v11 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v10)),
(@And (@Ne.{(0 + 1)} _v2 _v6 _v7) (@Exists.{(0 + 1)} (@Nat) (fun (_v12 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v2 (@instInhabitedProd.{0, 0}
  (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool)))) (fun (_v13 :
  (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v2 (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))))) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v12 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) _v10 _v8) _v8)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool)
  (@Option.{0} (@Bool))) _v2 (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))))) (@UniformClassBridgeClosure.Ordinary.trace _v2 _v4 _v5 _v12 (@Turing.TM0.init.{0,
  0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v2 _v4 (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool))
  (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) (@StandardTMBridgeClosure.encode (@List.ofFn.{0} (@Bool) _v10
  _v11)))) (@Option.some.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v2
  (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))))
  _v13)) (@And (@Eq.{(0 + 1)} _v2 (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v2
  (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) _v13)
  (@ite.{(0 + 1)} _v2 (@Eq.{(0 + 1)} (@Bool) (@UniformClassBridgeClosure.Ordinary.Verifies.match_1.{(0 + 1)} (fun (_v14 :
  (@Option.{0} (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))) =>
(@Bool)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.decodePair _v10 _v11) (fun (_v14 : (@Unit)) =>
(@Bool.false)) (fun (_v14 : (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair)) =>
(@_v1 (@Sigma.fst.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15)) (@Prod.fst.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15))) (@Sigma.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15))) _v14)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15)) (@Prod.snd.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15))) (@Sigma.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15))) _v14)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15)) (@Prod.fst.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15))) (@Sigma.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15))) _v14)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15)) (@Prod.snd.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15))) (@Sigma.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15))) _v14))))) (@Bool.true)) (@instDecidableEqBool
  (@UniformClassBridgeClosure.Ordinary.Verifies.match_1.{(0 + 1)} (fun (_v14 : (@Option.{0}
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))) =>
(@Bool)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.decodePair _v10 _v11) (fun (_v14 : (@Unit)) =>
(@Bool.false)) (fun (_v14 : (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair)) =>
(@_v1 (@Sigma.fst.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15)) (@Prod.fst.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15))) (@Sigma.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15))) _v14)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15)) (@Prod.snd.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15))) (@Sigma.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15))) _v14)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15)) (@Prod.fst.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15))) (@Sigma.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15))) _v14)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15)) (@Prod.snd.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15))) (@Sigma.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v15))) _v14))))) (@Bool.true)) _v6 _v7)) (@And (@Eq.{(0 + 1)} (@Option.{0}
  (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v2 (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))))) (@Turing.TM0.step.{0, 0} (@Prod.{0, 0} (@Bool)
  (@Option.{0} (@Bool))) _v2 _v4 (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))) _v5 _v13) (@Option.none.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool)
  (@Option.{0} (@Bool))) _v2 (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool)))))) (∀ (_v14 : (@Nat)),
(∀ (_v15 : (@LT.lt.{0} (@Nat) (@instLTNat) _v14 _v12)),
(∀ (_v16 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v2 (@instInhabitedProd.{0, 0} (@Bool)
  (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))))),
(∀ (_v17 : (@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v2
  (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool)))))
  (@UniformClassBridgeClosure.Ordinary.trace _v2 _v4 _v5 _v14 (@Turing.TM0.init.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0}
  (@Bool))) _v2 _v4 (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))) (@StandardTMBridgeClosure.encode (@List.ofFn.{0} (@Bool) _v10 _v11))))
  (@Option.some.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v2 (@instInhabitedProd.{0, 0}
  (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool)))) _v16))),
(@And (@Ne.{(0 + 1)} _v2 (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v2
  (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) _v16)
  _v6) (@Ne.{(0 + 1)} _v2 (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v2
  (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) _v16)
  _v7))))))))))))))))) (∀ (_v10 : (@Nat)),
(∀ (_v11 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v10)),
(@Iff (@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.ContentPrefixExtensionLanguage
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v10 _v11) (@Bool.true)) (@Exists.{(0 + 1)} (@Nat) (fun (_v12 :
  (@Nat)) =>
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v12) (fun (_v13 : (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v12)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v12 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) _v10 _v9) _v9)) (@Eq.{(0 + 1)} (@Bool) (@_v1 _v10 _v12 _v11 _v13)
  (@Bool.true)))))))))))))))))))))))))))))) := by
  exact @FullFinalClosure.ordinary_uniformNP_full

-- Independent literal expected type for FullFinalClosure.ordinary_verifier_full.
noncomputable def PartACanonical.Types.p0378 :
(∀ (_v0 : (@Nat)),
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
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0))) := by
  exact @FullFinalClosure.ordinary_verifier_full

-- Complete literal proposition for FullFinalClosure.ordinary_verifier_full; original proof reused.
theorem PartACanonical.Surface.m0231 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(@And (@Ne.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))))
  (@Option.some.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine
  _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@Prod.mk.{0, 0} (@Fin
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
  (4 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (0 : Nat))))))
  (@Exists.{(0 + 1)} (@Nat) (fun (_v3 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool)))) (fun (_v4 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool)))
  (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0)))
  (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))))) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v3 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) _v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))) (@FullFinalClosure.degree _v0)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))
  (@FullFinalClosure.degree _v0)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@And (@Eq.{(0 + 1)}
  (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))))) (@UniformClassBridgeClosure.Ordinary.trace (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))))) (@StandardTMBridgeClosure.compile (@FullFinalClosure.machine _v0)) _v3
  (@Turing.TM0.init.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))) (@StandardTMBridgeClosure.encode (@List.ofFn.{0} (@Bool) _v1 _v2))))
  (@Option.some.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool)))) _v4)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))))) (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) _v4) (@ite.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))))) (@Eq.{(0 + 1)} (@Bool) (@UniformClassBridgeClosure.Ordinary.Verifies.match_1.{(0 +
  1)} (fun (_v5 : (@Option.{0} (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))) =>
(@Bool)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.decodePair _v1 _v2) (fun (_v5 : (@Unit)) =>
(@Bool.false)) (fun (_v5 : (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair)) =>
(@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 (@Sigma.fst.{0, 0} (@Nat) (fun (_v6
  : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6)) (@Prod.fst.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6))) (@Sigma.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6))) _v5)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6)) (@Prod.snd.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6))) (@Sigma.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6)) (@Prod.fst.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6))) (@Sigma.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6)) (@Prod.snd.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6))) (@Sigma.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6))) _v5))))) (@Bool.true)) (@instDecidableEqBool
  (@UniformClassBridgeClosure.Ordinary.Verifies.match_1.{(0 + 1)} (fun (_v5 : (@Option.{0}
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))) =>
(@Bool)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.decodePair _v1 _v2) (fun (_v5 : (@Unit)) =>
(@Bool.false)) (fun (_v5 : (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair)) =>
(@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 (@Sigma.fst.{0, 0} (@Nat) (fun (_v6
  : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6)) (@Prod.fst.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6))) (@Sigma.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6))) _v5)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6)) (@Prod.snd.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6))) (@Sigma.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6)) (@Prod.fst.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6))) (@Sigma.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6))) _v5)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6)) (@Prod.snd.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6))) (@Sigma.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v6))) _v5))))) (@Bool.true)) (@Option.some.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@FullFinalClosure.machine _v0)) (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0}
  (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat
  (4 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (0 : Nat)))))
  (@Option.some.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine
  _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@Prod.mk.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@FullFinalClosure.machine _v0))
  (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (0 : Nat))))))) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0}
  (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))))
  (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool)))))
  (@Turing.TM0.step.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))) (@StandardTMBridgeClosure.compile (@FullFinalClosure.machine _v0)) _v4)
  (@Option.none.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool)))))) (∀ (_v5 : (@Nat)),
(∀ (_v6 : (@LT.lt.{0} (@Nat) (@instLTNat) _v5 _v3)),
(∀ (_v7 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))))),
(∀ (_v8 : (@Eq.{(0 + 1)} (@Option.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0}
  (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0}
  (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))))) (@UniformClassBridgeClosure.Ordinary.trace
  (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0)))
  (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))))) (@StandardTMBridgeClosure.compile (@FullFinalClosure.machine _v0)) _v5
  (@Turing.TM0.init.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))) (@StandardTMBridgeClosure.encode (@List.ofFn.{0} (@Bool) _v1 _v2))))
  (@Option.some.{0} (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool)))) _v7))),
(@And (@Ne.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))))
  (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool)
  (@instInhabitedOption.{0} (@Bool))) _v7) (@Option.some.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@FullFinalClosure.machine _v0)) (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0}
  (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat
  (4 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (0 : Nat)))))) (@Ne.{(0
  + 1)} (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine
  _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@Turing.TM0.Cfg.q.{0, 0} (@Prod.{0, 0}
  (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))))
  (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0} (@Bool))) _v7)
  (@Option.some.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine
  _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@Prod.mk.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@FullFinalClosure.machine _v0))) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@FullFinalClosure.machine _v0))
  (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (0 : Nat))))))))))))))))))))))) := by
  exact @FullFinalClosure.ordinary_verifier_full

-- Independent literal expected type for FullFinalClosure.raw_full.
noncomputable def PartACanonical.Types.p0379 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
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
  _v24)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @FullFinalClosure.raw_full

-- Complete literal proposition for FullFinalClosure.raw_full; original proof reused.
theorem PartACanonical.Surface.m0232 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
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
  _v24)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @FullFinalClosure.raw_full

-- Independent literal expected type for FullFinalClosure.right.
noncomputable def PartACanonical.Types.p0380 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@NormalFinalClosure.machine2 _v0)))),
(@Fin (@FullFinalClosure.count _v0)))) := by
  exact @FullFinalClosure.right

-- Independent literal expected type for FullFinalClosure.rows.
noncomputable def PartACanonical.Types.p0381 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@FullFinalClosure.count _v0))),
(∀ (_v2 : (@Option.{0} (@Bool))),
(@Prod.{0, 0} (@Fin (@FullFinalClosure.count _v0)) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)))))) := by
  exact @FullFinalClosure.rows

-- Independent literal expected type for FullFinalClosure.runtimeBound.
noncomputable def PartACanonical.Types.p0382 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(@Nat))) := by
  exact @FullFinalClosure.runtimeBound

-- Independent literal expected type for FullFinalClosure.uniformNP_full.
noncomputable def PartACanonical.Types.p0383 :
(∀ (_v0 : (@Nat)),
(@Pnp3.Complexity.Uniform.V1.UniformNP (@Pnp4.Frontier.ContractExpansion.ContentPrefixExtensionLanguage
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))))) := by
  exact @FullFinalClosure.uniformNP_full

-- Complete literal proposition for FullFinalClosure.uniformNP_full; original proof reused.
theorem PartACanonical.Surface.m0233 :
(∀ (_v0 : (@Nat)),
(@Pnp3.Complexity.Uniform.V1.UniformNP (@Pnp4.Frontier.ContractExpansion.ContentPrefixExtensionLanguage
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))))) := by
  exact @FullFinalClosure.uniformNP_full

-- Independent literal expected type for FullFinalClosure.verifier_full.
noncomputable def PartACanonical.Types.p0384 :
(∀ (_v0 : (@Nat)),
(@Pnp3.Complexity.Uniform.V1.VerifiesRelation (@FullFinalClosure.machine _v0) (@FullFinalClosure.degree _v0)
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0))) := by
  exact @FullFinalClosure.verifier_full

-- Complete literal proposition for FullFinalClosure.verifier_full; original proof reused.
theorem PartACanonical.Surface.m0234 :
(∀ (_v0 : (@Nat)),
(@Pnp3.Complexity.Uniform.V1.VerifiesRelation (@FullFinalClosure.machine _v0) (@FullFinalClosure.degree _v0)
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0))) := by
  exact @FullFinalClosure.verifier_full
