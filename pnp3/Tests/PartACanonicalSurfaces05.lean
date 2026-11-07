import Tests.PartACanonicalABI
import Tests.PartAG2InterfaceTests

/-! Infrastructure: mechanical literal restatements of this exact original API.
Proof terms are reused; these are not independently authored correctness proofs.
Type pins, theorem mirrors and direct roots remain separate manifests. -/
set_option autoImplicit false

-- Independent literal expected type for CappedWeight.check_phase_row.
noncomputable def PartACanonical.Types.p0256 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Option.{0} (@Bool))),
(∀ (_v4 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v0)),
(∀ (_v5 : (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (329 : Nat) (@instOfNatNat (329 : Nat))) _v1)),
(∀ (_v6 : (@LT.lt.{0} (@Nat) (@instLTNat) _v1 (@OfNat.ofNat.{0} (@Nat) (411 : Nat) (@instOfNatNat (411 : Nat))))),
(∀ (_v7 : (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@GetElem?.getElem?.{0, 0, 0} (@List.{0} (@Nat)) (@Nat) (@Nat) (fun (_v7 :
  (@List.{0} (@Nat))) =>
(fun (_v8 : (@Nat)) =>
(@LT.lt.{0} (@Nat) (@instLTNat) _v8 (@List.length.{0} (@Nat) _v7)))) (@List.instGetElem?NatLtLength.{0} (@Nat))
  (@CappedWeight.instructions _v0) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v1
  (@OfNat.ofNat.{0} (@Nat) (329 : Nat) (@instOfNatNat (329 : Nat))))) (@CappedWeight.check_phase_row.match_1.{(0 + 1)}
  (fun (_v7 : (@Option.{0} (@Bool))) =>
(@Nat)) _v3 (fun (_v7 : (@Unit)) =>
(@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (fun (_v7 : (@Unit)) =>
(@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (fun (_v7 : (@Unit)) =>
(@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))))) (@Option.some.{0} (@Nat) _v2))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))) (@Prod.{0,
  0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step
  (@Cursor.machine _v0) (@Cursor.q _v0 _v1) _v3) (@Prod.mk.{0, 0} (@Fin (@Cursor.stateCount _v0)) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.q _v0 (@HDiv.hDiv.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHDiv.{0} (@Nat) (@Nat.instDiv)) _v2 (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))))) (@Prod.mk.{0,
  0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat)
  (@HMod.hMod.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMod.{0} (@Nat) (@Nat.instMod)) (@HDiv.hDiv.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHDiv.{0} (@Nat) (@Nat.instDiv)) _v2 (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat)))) (@instDecidableEqNat (@HMod.hMod.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMod.{0} (@Nat) (@Nat.instMod))
  (@HDiv.hDiv.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHDiv.{0} (@Nat) (@Nat.instDiv)) _v2 (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 :
  Nat) (@instOfNatNat (0 : Nat)))) (@Option.none.{0} (@Bool)) (@Option.some.{0} (@Bool) (@Decidable.decide (@Eq.{(0 + 1)}
  (@Nat) (@HMod.hMod.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMod.{0} (@Nat) (@Nat.instMod)) (@HDiv.hDiv.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHDiv.{0} (@Nat) (@Nat.instDiv)) _v2 (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat)))) (@instDecidableEqNat (@HMod.hMod.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMod.{0} (@Nat) (@Nat.instMod))
  (@HDiv.hDiv.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHDiv.{0} (@Nat) (@Nat.instDiv)) _v2 (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))))))) (@ite.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Move) (@Eq.{(0 + 1)} (@Nat)
  (@HMod.hMod.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMod.{0} (@Nat) (@Nat.instMod)) _v2 (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat
  (@HMod.hMod.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMod.{0} (@Nat) (@Nat.instMod)) _v2 (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.Move.left) (@ite.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Move) (@Eq.{(0 + 1)} (@Nat)
  (@HMod.hMod.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMod.{0} (@Nat) (@Nat.instMod)) _v2 (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@instDecidableEqNat
  (@HMod.hMod.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMod.{0} (@Nat) (@Nat.instMod)) _v2 (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.Move.stay) (@Pnp3.Complexity.Uniform.V1.Move.right)))))))))))))) := by
  exact @CappedWeight.check_phase_row

-- Complete literal proposition for CappedWeight.check_phase_row; original proof reused.
theorem PartACanonical.Surface.m0162 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Option.{0} (@Bool))),
(∀ (_v4 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v0)),
(∀ (_v5 : (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (329 : Nat) (@instOfNatNat (329 : Nat))) _v1)),
(∀ (_v6 : (@LT.lt.{0} (@Nat) (@instLTNat) _v1 (@OfNat.ofNat.{0} (@Nat) (411 : Nat) (@instOfNatNat (411 : Nat))))),
(∀ (_v7 : (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@GetElem?.getElem?.{0, 0, 0} (@List.{0} (@Nat)) (@Nat) (@Nat) (fun (_v7 :
  (@List.{0} (@Nat))) =>
(fun (_v8 : (@Nat)) =>
(@LT.lt.{0} (@Nat) (@instLTNat) _v8 (@List.length.{0} (@Nat) _v7)))) (@List.instGetElem?NatLtLength.{0} (@Nat))
  (@CappedWeight.instructions _v0) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v1
  (@OfNat.ofNat.{0} (@Nat) (329 : Nat) (@instOfNatNat (329 : Nat))))) (@CappedWeight.check_phase_row.match_1.{(0 + 1)}
  (fun (_v7 : (@Option.{0} (@Bool))) =>
(@Nat)) _v3 (fun (_v7 : (@Unit)) =>
(@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (fun (_v7 : (@Unit)) =>
(@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (fun (_v7 : (@Unit)) =>
(@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))))) (@Option.some.{0} (@Nat) _v2))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))) (@Prod.{0,
  0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step
  (@Cursor.machine _v0) (@Cursor.q _v0 _v1) _v3) (@Prod.mk.{0, 0} (@Fin (@Cursor.stateCount _v0)) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Cursor.q _v0 (@HDiv.hDiv.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHDiv.{0} (@Nat) (@Nat.instDiv)) _v2 (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))))) (@Prod.mk.{0,
  0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat)
  (@HMod.hMod.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMod.{0} (@Nat) (@Nat.instMod)) (@HDiv.hDiv.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHDiv.{0} (@Nat) (@Nat.instDiv)) _v2 (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat)))) (@instDecidableEqNat (@HMod.hMod.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMod.{0} (@Nat) (@Nat.instMod))
  (@HDiv.hDiv.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHDiv.{0} (@Nat) (@Nat.instDiv)) _v2 (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 :
  Nat) (@instOfNatNat (0 : Nat)))) (@Option.none.{0} (@Bool)) (@Option.some.{0} (@Bool) (@Decidable.decide (@Eq.{(0 + 1)}
  (@Nat) (@HMod.hMod.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMod.{0} (@Nat) (@Nat.instMod)) (@HDiv.hDiv.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHDiv.{0} (@Nat) (@Nat.instDiv)) _v2 (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat)))) (@instDecidableEqNat (@HMod.hMod.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMod.{0} (@Nat) (@Nat.instMod))
  (@HDiv.hDiv.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHDiv.{0} (@Nat) (@Nat.instDiv)) _v2 (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))))))) (@ite.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Move) (@Eq.{(0 + 1)} (@Nat)
  (@HMod.hMod.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMod.{0} (@Nat) (@Nat.instMod)) _v2 (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat
  (@HMod.hMod.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMod.{0} (@Nat) (@Nat.instMod)) _v2 (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.Move.left) (@ite.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Move) (@Eq.{(0 + 1)} (@Nat)
  (@HMod.hMod.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMod.{0} (@Nat) (@Nat.instMod)) _v2 (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@instDecidableEqNat
  (@HMod.hMod.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMod.{0} (@Nat) (@Nat.instMod)) _v2 (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.Move.stay) (@Pnp3.Complexity.Uniform.V1.Move.right)))))))))))))) := by
  exact @CappedWeight.check_phase_row

-- Independent literal expected type for CappedWeight.first_product.
noncomputable def PartACanonical.Types.p0257 :
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
(∀ (_v9 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v0)),
(∀ (_v10 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v7)),
(∀ (_v11 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v5)),
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))) _v5) _v6)),
(∀ (_v13 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v8 _v3) (@Option.none.{0} (@Bool)))),
(∀ (_v14 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v8 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Option.none.{0} (@Bool)))),
(∀ (_v15 : (∀ (_v15 : (@Nat)),
(∀ (_v16 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v15)),
(∀ (_v17 : (@LE.le.{0} (@Nat) (@instLENat) _v15 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))) _v5))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v8 _v15) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v16 : (∀ (_v16 : (@Nat)),
(∀ (_v17 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))) _v5) _v16)),
(∀ (_v18 : (@LT.lt.{0} (@Nat) (@instLTNat) _v16 _v6)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v8 _v16) (@Option.none.{0} (@Bool))))))),
(∀ (_v17 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v8 _v6) (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v18 : (∀ (_v18 : (@Nat)),
(∀ (_v19 : (@Or (@Eq.{(0 + 1)} (@Nat) _v18 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Or (@Eq.{(0 + 1)} (@Nat) _v18
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 _v7) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))
  (@Or (@Eq.{(0 + 1)} (@Nat) _v18 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 _v7) _v4) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 :
  Nat))))) (@Or (@Eq.{(0 + 1)} (@Nat) _v18 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v7)) _v4) (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat))))) (@Or (@Eq.{(0 + 1)} (@Nat) _v18 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v7)) _v4)
  (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))) (@Or (@Eq.{(0 + 1)} (@Nat) _v18 (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))) _v7)) _v4) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))) (@Eq.{(0 + 1)}
  (@Nat) _v18 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v6 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v7)) _v4) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 :
  Nat)))))))))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v8 _v18) (@Option.none.{0} (@Bool)))))),
(∀ (_v19 : (∀ (_v19 : (@Nat)),
(∀ (_v20 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v19)),
(∀ (_v21 : (@LT.lt.{0} (@Nat) (@instLTNat) _v19 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 _v7)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v8 _v19) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v20 : (∀ (_v20 : (@Nat)),
(∀ (_v21 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 _v7)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v20)),
(∀ (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat) _v20 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 _v7) _v4) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v8 _v20) (@Option.some.{0} (@Bool) (@Bool.false))))))),
(∀ (_v21 : (@Eq.{(0 + 1)} (∀ (_v21 : (@Nat)),
(@Option.{0} (@Bool))) (@CappedWeight.Target.image _v8 _v3 _v4 _v6 _v7 (@Pnp4.Frontier.ContractExpansion.bitLength _v4)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat)))) _v8)),
(@CappedWeight.Target.FirstProduct _v0 _v1 _v2 _v3 _v4 _v6 _v7 _v8))))))))))))))))))))))) := by
  exact @CappedWeight.first_product

-- Complete literal proposition for CappedWeight.first_product; original proof reused.
theorem PartACanonical.Surface.m0163 :
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
(∀ (_v9 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v0)),
(∀ (_v10 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v7)),
(∀ (_v11 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v5)),
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))) _v5) _v6)),
(∀ (_v13 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v8 _v3) (@Option.none.{0} (@Bool)))),
(∀ (_v14 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v8 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Option.none.{0} (@Bool)))),
(∀ (_v15 : (∀ (_v15 : (@Nat)),
(∀ (_v16 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v15)),
(∀ (_v17 : (@LE.le.{0} (@Nat) (@instLENat) _v15 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))) _v5))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v8 _v15) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v16 : (∀ (_v16 : (@Nat)),
(∀ (_v17 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))) _v5) _v16)),
(∀ (_v18 : (@LT.lt.{0} (@Nat) (@instLTNat) _v16 _v6)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v8 _v16) (@Option.none.{0} (@Bool))))))),
(∀ (_v17 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v8 _v6) (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v18 : (∀ (_v18 : (@Nat)),
(∀ (_v19 : (@Or (@Eq.{(0 + 1)} (@Nat) _v18 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Or (@Eq.{(0 + 1)} (@Nat) _v18
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 _v7) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))
  (@Or (@Eq.{(0 + 1)} (@Nat) _v18 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 _v7) _v4) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 :
  Nat))))) (@Or (@Eq.{(0 + 1)} (@Nat) _v18 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v7)) _v4) (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat))))) (@Or (@Eq.{(0 + 1)} (@Nat) _v18 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v7)) _v4)
  (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))) (@Or (@Eq.{(0 + 1)} (@Nat) _v18 (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))) _v7)) _v4) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))) (@Eq.{(0 + 1)}
  (@Nat) _v18 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v6 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v7)) _v4) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 :
  Nat)))))))))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v8 _v18) (@Option.none.{0} (@Bool)))))),
(∀ (_v19 : (∀ (_v19 : (@Nat)),
(∀ (_v20 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v19)),
(∀ (_v21 : (@LT.lt.{0} (@Nat) (@instLTNat) _v19 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 _v7)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v8 _v19) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v20 : (∀ (_v20 : (@Nat)),
(∀ (_v21 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 _v7)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v20)),
(∀ (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat) _v20 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 _v7) _v4) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v8 _v20) (@Option.some.{0} (@Bool) (@Bool.false))))))),
(∀ (_v21 : (@Eq.{(0 + 1)} (∀ (_v21 : (@Nat)),
(@Option.{0} (@Bool))) (@CappedWeight.Target.image _v8 _v3 _v4 _v6 _v7 (@Pnp4.Frontier.ContractExpansion.bitLength _v4)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat)))) _v8)),
(∀ (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v7)) _v4) (@OfNat.ofNat.{0} (@Nat)
  (7 : Nat) (@instOfNatNat (7 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))),
(@Exists.{(0 + 1)} (@Nat) (fun (_v23 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v23 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (1024 : Nat) (@instOfNatNat (1024 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 _v7)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v6 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v7)) _v4) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))))))
  (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Cursor.machine _v0)) _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Cursor.machine _v0) _v1 _v2 _v23
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0)) _v1 _v2
  (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (329 : Nat) (@instOfNatNat (329 : Nat)))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v7)) _v4) (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))) (@CappedWeight.Target.FirstProduct._proof_4 _v1 _v2 _v4 _v6 _v7 _v22)) (fun (_v24
  : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))) =>
(@_v8 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) _v24))))) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0)) _v1 _v2 (@Cursor.q _v0 (@ite.{(0 + 1)} (@Nat)
  (@LE.le.{0} (@Nat) (@instLENat) _v4 _v7) (@Nat.decLe _v4 _v7) (@OfNat.ofNat.{0} (@Nat) (411 : Nat) (@instOfNatNat (411 :
  Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (798 :
  Nat) (@instOfNatNat (798 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (93 : Nat) (@instOfNatNat (93 : Nat))) _v0)))) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v1 _v2) (@ite.{(0 + 1)} (@Nat) (@LE.le.{0} (@Nat) (@instLENat) _v4 _v7) (@Nat.decLe _v4 _v7) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v7)) _v4) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat))))) (@CappedWeight.Target.FirstProduct._proof_5 _v1 _v2 _v4 _v6 _v7 _v22)) (fun (_v24 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))) =>
(@CappedWeight.Target.image _v8 _v3 _v4 _v6 _v7 (@Pnp4.Frontier.ContractExpansion.bitLength _v4) (@ite.{(0 + 1)} (@Nat)
  (@LE.le.{0} (@Nat) (@instLENat) _v4 _v7) (@Nat.decLe _v4 _v7) _v4 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat)))) (@ite.{(0 + 1)} (@Nat) (@LE.le.{0} (@Nat) (@instLENat) _v4 _v7) (@Nat.decLe _v4 _v7) (@OfNat.ofNat.{0} (@Nat) (0
  : Nat) (@instOfNatNat (0 : Nat))) _v7) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@ite.{(0 + 1)}
  (@Nat) (@LE.le.{0} (@Nat) (@instLENat) _v4 _v7) (@Nat.decLe _v4 _v7) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v7 (@OfNat.ofNat.{0} (@Nat)
  (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) _v24))))) (∀ (_v24 :
  (@Nat)),
(∀ (_v25 : (@LT.lt.{0} (@Nat) (@instLTNat) _v24 _v23)),
(@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0)) _v1
  _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Cursor.machine _v0) _v1 _v2 _v24 (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0)) _v1 _v2 (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat)
  (329 : Nat) (@instOfNatNat (329 : Nat)))) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v7)) _v4) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))
  (@CappedWeight.Target.FirstProduct._proof_4 _v1 _v2 _v4 _v6 _v7 _v22)) (fun (_v26 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))) =>
(@_v8 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) _v26))))))) (@OfNat.ofNat.{0} (@Nat) (411 : Nat)
  (@instOfNatNat (411 : Nat))))))))))))))))))))))))))))))))) := by
  exact @CappedWeight.first_product

-- Independent literal expected type for CappedWeight.instructions.
noncomputable def PartACanonical.Types.p0258 :
(∀ (_v0 : (@Nat)),
(@List.{0} (@Nat))) := by
  exact @CappedWeight.instructions

-- Independent literal expected type for CappedWeight.instructions.eq_1.
noncomputable def PartACanonical.Types.p0259 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@List.{0} (@Nat)) (@CappedWeight.instructions _v0) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (2972
  : Nat) (@instOfNatNat (2972 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (2975 : Nat) (@instOfNatNat (2975 :
  Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (2978 : Nat) (@instOfNatNat (2978 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (2979 : Nat) (@instOfNatNat (2979 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (2982 : Nat) (@instOfNatNat (2982 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (2978 : Nat) (@instOfNatNat
  (2978 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3430 : Nat) (@instOfNatNat (3430 : Nat))) (let _v1 :
  (@List.{0} (@Nat)) := (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (2994 : Nat) (@instOfNatNat (2994 : Nat)))
  (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3006 : Nat) (@instOfNatNat (3006 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3009 : Nat) (@instOfNatNat (3009 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3012 : Nat) (@instOfNatNat (3012 : Nat))) (let _v1 : (@List.{0} (@Nat)) := (let _v1 : (@List.{0} (@Nat)) :=
  (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3048 : Nat) (@instOfNatNat (3048 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3052 : Nat) (@instOfNatNat (3052 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3045 : Nat) (@instOfNatNat (3045 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3048 : Nat) (@instOfNatNat
  (3048 : Nat))) (let _v1 : (@List.{0} (@Nat)) := (let _v1 : (@List.{0} (@Nat)) := (let _v1 : (@List.{0} (@Nat)) :=
  (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3143 : Nat) (@instOfNatNat (3143 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3146 : Nat) (@instOfNatNat (3146 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3149 : Nat) (@instOfNatNat (3149 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3151 : Nat) (@instOfNatNat
  (3151 : Nat))) (let _v1 : (@List.{0} (@Nat)) := (let _v1 : (@List.{0} (@Nat)) := (let _v1 : (@List.{0} (@Nat)) := (let
  _v1 : (@List.{0} (@Nat)) := (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3327 : Nat) (@instOfNatNat (3327 : Nat)))
  (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (361 : Nat) (@instOfNatNat (361 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3333 : Nat) (@instOfNatNat (3333 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (367
  : Nat) (@instOfNatNat (367 : Nat))) (let _v1 : (@List.{0} (@Nat)) := (let _v1 : (@List.{0} (@Nat)) := (let _v1 :
  (@List.{0} (@Nat)) := (let _v1 : (@List.{0} (@Nat)) := (let _v1 : (@List.{0} (@Nat)) := (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3696 : Nat) (@instOfNatNat (3696 : Nat))) (@List.cons.{0} (@Nat) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (7183 : Nat) (@instOfNatNat (7183 : Nat)))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (837 : Nat)
  (@instOfNatNat (837 : Nat))) _v0)) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3693 : Nat) (@instOfNatNat (3693 :
  Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3696 : Nat) (@instOfNatNat (3696 : Nat))) (@List.nil.{0}
  (@Nat))))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3675 : Nat) (@instOfNatNat (3675 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3678 : Nat) (@instOfNatNat (3678 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3690 : Nat) (@instOfNatNat (3690 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3693 : Nat) (@instOfNatNat
  (3693 : Nat))) _v1)))));
(let _v2 : (@List.{0} (@Nat)) := (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3672 : Nat) (@instOfNatNat (3672 :
  Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3675 : Nat) (@instOfNatNat (3675 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3678 : Nat) (@instOfNatNat (3678 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3682 : Nat) (@instOfNatNat (3682 : Nat))) _v1))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3660 : Nat) (@instOfNatNat (3660 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3664 : Nat) (@instOfNatNat (3664 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3657 : Nat) (@instOfNatNat (3657 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3660 : Nat) (@instOfNatNat
  (3660 : Nat))) _v2))))));
(let _v2 : (@List.{0} (@Nat)) := (let _v2 : (@List.{0} (@Nat)) := (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3639
  : Nat) (@instOfNatNat (3639 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3642 : Nat) (@instOfNatNat (3642 :
  Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3654 : Nat) (@instOfNatNat (3654 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3657 : Nat) (@instOfNatNat (3657 : Nat))) _v1))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3636 : Nat) (@instOfNatNat (3636 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3639 : Nat) (@instOfNatNat (3639 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3642 : Nat) (@instOfNatNat (3642 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3646 : Nat) (@instOfNatNat
  (3646 : Nat))) _v2)))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3606 : Nat) (@instOfNatNat (3606 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3618 : Nat) (@instOfNatNat (3618 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3621 : Nat) (@instOfNatNat (3621 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3624 : Nat) (@instOfNatNat
  (3624 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3700 : Nat) (@instOfNatNat (3700 : Nat)))
  (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3621 : Nat) (@instOfNatNat (3621 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3624 : Nat) (@instOfNatNat (3624 : Nat))) _v2)))))))));
(let _v2 : (@List.{0} (@Nat)) := (let _v2 : (@List.{0} (@Nat)) := (let _v2 : (@List.{0} (@Nat)) := (@List.cons.{0}
  (@Nat) (@OfNat.ofNat.{0} (@Nat) (3603 : Nat) (@instOfNatNat (3603 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0}
  (@Nat) (3606 : Nat) (@instOfNatNat (3606 : Nat))) (@List.cons.{0} (@Nat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (7183 : Nat) (@instOfNatNat (7183 : Nat))) (@HMul.hMul.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (837 : Nat) (@instOfNatNat (837
  : Nat))) _v0)) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3603 : Nat) (@instOfNatNat (3603 : Nat))) _v1))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3592 : Nat) (@instOfNatNat (3592 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3585 : Nat) (@instOfNatNat (3585 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3588 : Nat) (@instOfNatNat (3588 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3600 : Nat) (@instOfNatNat
  (3600 : Nat))) _v2)))));
(let _v3 : (@List.{0} (@Nat)) := (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3570 : Nat) (@instOfNatNat (3570 :
  Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3582 : Nat) (@instOfNatNat (3582 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3585 : Nat) (@instOfNatNat (3585 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3588 : Nat) (@instOfNatNat (3588 : Nat))) _v2))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3567 : Nat) (@instOfNatNat (3567 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3570 : Nat) (@instOfNatNat (3570 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3574 : Nat) (@instOfNatNat (3574 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3567 : Nat) (@instOfNatNat
  (3567 : Nat))) _v3))))));
(let _v3 : (@List.{0} (@Nat)) := (let _v3 : (@List.{0} (@Nat)) := (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3448
  : Nat) (@instOfNatNat (3448 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3551 : Nat) (@instOfNatNat (3551 :
  Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3554 : Nat) (@instOfNatNat (3554 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3564 : Nat) (@instOfNatNat (3564 : Nat))) _v2))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3534 : Nat) (@instOfNatNat (3534 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3548 : Nat) (@instOfNatNat (3548 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3551 : Nat) (@instOfNatNat (3551 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3554 : Nat) (@instOfNatNat
  (3554 : Nat))) _v3)))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3525 : Nat) (@instOfNatNat (3525 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3518 : Nat) (@instOfNatNat (3518 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3538 : Nat) (@instOfNatNat (3538 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3522 : Nat) (@instOfNatNat
  (3522 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3525 : Nat) (@instOfNatNat (3525 : Nat)))
  (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3556 : Nat) (@instOfNatNat (3556 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3531 : Nat) (@instOfNatNat (3531 : Nat))) _v3))))))))));
(let _v2 : (@List.{0} (@Nat)) := (let _v2 : (@List.{0} (@Nat)) := (let _v2 : (@List.{0} (@Nat)) := (let _v2 : (@List.{0}
  (@Nat)) := (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3512 : Nat) (@instOfNatNat (3512 : Nat))) (@List.cons.{0}
  (@Nat) (@OfNat.ofNat.{0} (@Nat) (3515 : Nat) (@instOfNatNat (3515 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0}
  (@Nat) (3518 : Nat) (@instOfNatNat (3518 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3528 : Nat)
  (@instOfNatNat (3528 : Nat))) _v1))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3498 : Nat) (@instOfNatNat (3498 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3502 : Nat) (@instOfNatNat (3502 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3495 : Nat) (@instOfNatNat (3495 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3498 : Nat) (@instOfNatNat
  (3498 : Nat))) _v2)))));
(let _v3 : (@List.{0} (@Nat)) := (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3477 : Nat) (@instOfNatNat (3477 :
  Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3480 : Nat) (@instOfNatNat (3480 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3492 : Nat) (@instOfNatNat (3492 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3495 : Nat) (@instOfNatNat (3495 : Nat))) _v2))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3610 : Nat) (@instOfNatNat (3610 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (364 : Nat) (@instOfNatNat (364 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3477
  : Nat) (@instOfNatNat (3477 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3484 : Nat) (@instOfNatNat (3484 :
  Nat))) _v3))))));
(let _v3 : (@List.{0} (@Nat)) := (let _v3 : (@List.{0} (@Nat)) := (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3464
  : Nat) (@instOfNatNat (3464 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3465 : Nat) (@instOfNatNat (3465 :
  Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3468 : Nat) (@instOfNatNat (3468 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3464 : Nat) (@instOfNatNat (3464 : Nat))) _v2))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3443 : Nat) (@instOfNatNat (3443 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3446 : Nat) (@instOfNatNat (3446 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3458 : Nat) (@instOfNatNat (3458 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3461 : Nat) (@instOfNatNat
  (3461 : Nat))) _v3)))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (2962 : Nat) (@instOfNatNat (2962 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3425 : Nat) (@instOfNatNat (3425 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3428 : Nat) (@instOfNatNat (3428 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3440 : Nat) (@instOfNatNat
  (3440 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3443 : Nat) (@instOfNatNat (3443 : Nat)))
  (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3446 : Nat) (@instOfNatNat (3446 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3448 : Nat) (@instOfNatNat (3448 : Nat))) _v3)))))))));
(let _v3 : (@List.{0} (@Nat)) := (let _v3 : (@List.{0} (@Nat)) := (let _v3 : (@List.{0} (@Nat)) := (@List.cons.{0}
  (@Nat) (@OfNat.ofNat.{0} (@Nat) (3410 : Nat) (@instOfNatNat (3410 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0}
  (@Nat) (3422 : Nat) (@instOfNatNat (3422 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3425 : Nat)
  (@instOfNatNat (3425 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3428 : Nat) (@instOfNatNat (3428 : Nat)))
  _v2))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3407 : Nat) (@instOfNatNat (3407 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3410 : Nat) (@instOfNatNat (3410 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3412 : Nat) (@instOfNatNat (3412 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3407 : Nat) (@instOfNatNat
  (3407 : Nat))) _v3)))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3386 : Nat) (@instOfNatNat (3386 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3389 : Nat) (@instOfNatNat (3389 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3392 : Nat) (@instOfNatNat (3392 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3394 : Nat) (@instOfNatNat
  (3394 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3389 : Nat) (@instOfNatNat (3389 : Nat)))
  (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3392 : Nat) (@instOfNatNat (3392 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3404 : Nat) (@instOfNatNat (3404 : Nat))) _v3))))))));
(let _v4 : (@List.{0} (@Nat)) := (let _v4 : (@List.{0} (@Nat)) := (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3374
  : Nat) (@instOfNatNat (3374 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3368 : Nat) (@instOfNatNat (3368 :
  Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3380 : Nat) (@instOfNatNat (3380 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3374 : Nat) (@instOfNatNat (3374 : Nat))) _v3))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3353 : Nat) (@instOfNatNat (3353 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3353 : Nat) (@instOfNatNat (3353 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3368 : Nat) (@instOfNatNat (3368 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3371 : Nat) (@instOfNatNat
  (3371 : Nat))) _v4)))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3330 : Nat) (@instOfNatNat (3330 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (364 : Nat) (@instOfNatNat (364 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3345
  : Nat) (@instOfNatNat (3345 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3088 : Nat) (@instOfNatNat (3088 :
  Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (364 : Nat) (@instOfNatNat (364 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3345 : Nat) (@instOfNatNat (3345 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3358 : Nat) (@instOfNatNat (3358 : Nat))) _v4)))))))))))))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3306 : Nat) (@instOfNatNat (3306 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3309 : Nat) (@instOfNatNat (3309 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3321 : Nat) (@instOfNatNat (3321 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3324 : Nat) (@instOfNatNat
  (3324 : Nat))) _v1)))));
(let _v2 : (@List.{0} (@Nat)) := (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3303 : Nat) (@instOfNatNat (3303 :
  Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3306 : Nat) (@instOfNatNat (3306 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3309 : Nat) (@instOfNatNat (3309 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3313 : Nat) (@instOfNatNat (3313 : Nat))) _v1))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3291 : Nat) (@instOfNatNat (3291 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3295 : Nat) (@instOfNatNat (3295 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3288 : Nat) (@instOfNatNat (3288 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3291 : Nat) (@instOfNatNat
  (3291 : Nat))) _v2))))));
(let _v2 : (@List.{0} (@Nat)) := (let _v2 : (@List.{0} (@Nat)) := (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3270
  : Nat) (@instOfNatNat (3270 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3273 : Nat) (@instOfNatNat (3273 :
  Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3285 : Nat) (@instOfNatNat (3285 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3288 : Nat) (@instOfNatNat (3288 : Nat))) _v1))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3267 : Nat) (@instOfNatNat (3267 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3270 : Nat) (@instOfNatNat (3270 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3273 : Nat) (@instOfNatNat (3273 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3277 : Nat) (@instOfNatNat
  (3277 : Nat))) _v2)))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3237 : Nat) (@instOfNatNat (3237 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3249 : Nat) (@instOfNatNat (3249 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3252 : Nat) (@instOfNatNat (3252 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3255 : Nat) (@instOfNatNat
  (3255 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3259 : Nat) (@instOfNatNat (3259 : Nat)))
  (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3252 : Nat) (@instOfNatNat (3252 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3255 : Nat) (@instOfNatNat (3255 : Nat))) _v2)))))))));
(let _v2 : (@List.{0} (@Nat)) := (let _v2 : (@List.{0} (@Nat)) := (let _v2 : (@List.{0} (@Nat)) := (@List.cons.{0}
  (@Nat) (@OfNat.ofNat.{0} (@Nat) (3225 : Nat) (@instOfNatNat (3225 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0}
  (@Nat) (3228 : Nat) (@instOfNatNat (3228 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3628 : Nat)
  (@instOfNatNat (3628 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3234 : Nat) (@instOfNatNat (3234 : Nat)))
  _v1))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3231 : Nat) (@instOfNatNat (3231 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3228 : Nat) (@instOfNatNat (3228 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3221 : Nat) (@instOfNatNat (3221 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3241 : Nat) (@instOfNatNat
  (3241 : Nat))) _v2)))));
(let _v3 : (@List.{0} (@Nat)) := (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3203 : Nat) (@instOfNatNat (3203 :
  Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3215 : Nat) (@instOfNatNat (3215 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3218 : Nat) (@instOfNatNat (3218 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3221 : Nat) (@instOfNatNat (3221 : Nat))) _v2))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3200 : Nat) (@instOfNatNat (3200 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3203 : Nat) (@instOfNatNat (3203 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3205 : Nat) (@instOfNatNat (3205 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3200 : Nat) (@instOfNatNat
  (3200 : Nat))) _v3))))));
(let _v3 : (@List.{0} (@Nat)) := (let _v3 : (@List.{0} (@Nat)) := (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3187
  : Nat) (@instOfNatNat (3187 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3182 : Nat) (@instOfNatNat (3182 :
  Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3185 : Nat) (@instOfNatNat (3185 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3197 : Nat) (@instOfNatNat (3197 : Nat))) _v2))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3167 : Nat) (@instOfNatNat (3167 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3179 : Nat) (@instOfNatNat (3179 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3182 : Nat) (@instOfNatNat (3182 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3185 : Nat) (@instOfNatNat
  (3185 : Nat))) _v3)))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3146 : Nat) (@instOfNatNat (3146 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3149 : Nat) (@instOfNatNat (3149 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3161 : Nat) (@instOfNatNat (3161 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3164 : Nat) (@instOfNatNat
  (3164 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3167 : Nat) (@instOfNatNat (3167 : Nat)))
  (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3169 : Nat) (@instOfNatNat (3169 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3164 : Nat) (@instOfNatNat (3164 : Nat))) _v3))))))))))))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3131 : Nat) (@instOfNatNat (3131 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3125 : Nat) (@instOfNatNat (3125 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3137 : Nat) (@instOfNatNat (3137 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3131 : Nat) (@instOfNatNat
  (3131 : Nat))) _v1)))));
(let _v2 : (@List.{0} (@Nat)) := (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3110 : Nat) (@instOfNatNat (3110 :
  Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3113 : Nat) (@instOfNatNat (3113 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3125 : Nat) (@instOfNatNat (3125 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3128 : Nat) (@instOfNatNat (3128 : Nat))) _v1))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3350 : Nat) (@instOfNatNat (3350 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3113 : Nat) (@instOfNatNat (3113 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3102 : Nat) (@instOfNatNat (3102 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3115 : Nat) (@instOfNatNat
  (3115 : Nat))) _v2))))));
(let _v2 : (@List.{0} (@Nat)) := (let _v2 : (@List.{0} (@Nat)) := (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3084
  : Nat) (@instOfNatNat (3084 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3096 : Nat) (@instOfNatNat (3096 :
  Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3099 : Nat) (@instOfNatNat (3099 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3102 : Nat) (@instOfNatNat (3102 : Nat))) _v1))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (364 : Nat) (@instOfNatNat (364 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3084 : Nat) (@instOfNatNat (3084 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3088 : Nat) (@instOfNatNat (3088 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (364 : Nat) (@instOfNatNat
  (364 : Nat))) _v2)))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3060 : Nat) (@instOfNatNat (3060 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3063 : Nat) (@instOfNatNat (3063 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3066 : Nat) (@instOfNatNat (3066 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (361 : Nat) (@instOfNatNat
  (361 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3072 : Nat) (@instOfNatNat (3072 : Nat))) (@List.cons.{0}
  (@Nat) (@OfNat.ofNat.{0} (@Nat) (367 : Nat) (@instOfNatNat (367 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3069 : Nat) (@instOfNatNat (3069 : Nat))) _v2)))))))))))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3027 : Nat) (@instOfNatNat (3027 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3030 : Nat) (@instOfNatNat (3030 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3042 : Nat) (@instOfNatNat (3042 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3045 : Nat) (@instOfNatNat
  (3045 : Nat))) _v1)))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3016 : Nat) (@instOfNatNat (3016 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3009 : Nat) (@instOfNatNat (3009 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3012 : Nat) (@instOfNatNat (3012 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3024 : Nat) (@instOfNatNat
  (3024 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3027 : Nat) (@instOfNatNat (3027 : Nat)))
  (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3030 : Nat) (@instOfNatNat (3030 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3034 : Nat) (@instOfNatNat (3034 : Nat))) _v1))))))))))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (364 : Nat) (@instOfNatNat (364 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (2991 : Nat) (@instOfNatNat (2991 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (2998 : Nat) (@instOfNatNat (2998 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (2991 : Nat) (@instOfNatNat
  (2991 : Nat))) _v1)))))))))))))) := by
  exact @CappedWeight.instructions.eq_1

-- Complete literal proposition for CappedWeight.instructions.eq_1; original proof reused.
theorem PartACanonical.Surface.m0164 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@List.{0} (@Nat)) (@CappedWeight.instructions _v0) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (2972
  : Nat) (@instOfNatNat (2972 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (2975 : Nat) (@instOfNatNat (2975 :
  Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (2978 : Nat) (@instOfNatNat (2978 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (2979 : Nat) (@instOfNatNat (2979 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (2982 : Nat) (@instOfNatNat (2982 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (2978 : Nat) (@instOfNatNat
  (2978 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3430 : Nat) (@instOfNatNat (3430 : Nat))) (let _v1 :
  (@List.{0} (@Nat)) := (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (2994 : Nat) (@instOfNatNat (2994 : Nat)))
  (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3006 : Nat) (@instOfNatNat (3006 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3009 : Nat) (@instOfNatNat (3009 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3012 : Nat) (@instOfNatNat (3012 : Nat))) (let _v1 : (@List.{0} (@Nat)) := (let _v1 : (@List.{0} (@Nat)) :=
  (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3048 : Nat) (@instOfNatNat (3048 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3052 : Nat) (@instOfNatNat (3052 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3045 : Nat) (@instOfNatNat (3045 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3048 : Nat) (@instOfNatNat
  (3048 : Nat))) (let _v1 : (@List.{0} (@Nat)) := (let _v1 : (@List.{0} (@Nat)) := (let _v1 : (@List.{0} (@Nat)) :=
  (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3143 : Nat) (@instOfNatNat (3143 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3146 : Nat) (@instOfNatNat (3146 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3149 : Nat) (@instOfNatNat (3149 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3151 : Nat) (@instOfNatNat
  (3151 : Nat))) (let _v1 : (@List.{0} (@Nat)) := (let _v1 : (@List.{0} (@Nat)) := (let _v1 : (@List.{0} (@Nat)) := (let
  _v1 : (@List.{0} (@Nat)) := (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3327 : Nat) (@instOfNatNat (3327 : Nat)))
  (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (361 : Nat) (@instOfNatNat (361 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3333 : Nat) (@instOfNatNat (3333 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (367
  : Nat) (@instOfNatNat (367 : Nat))) (let _v1 : (@List.{0} (@Nat)) := (let _v1 : (@List.{0} (@Nat)) := (let _v1 :
  (@List.{0} (@Nat)) := (let _v1 : (@List.{0} (@Nat)) := (let _v1 : (@List.{0} (@Nat)) := (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3696 : Nat) (@instOfNatNat (3696 : Nat))) (@List.cons.{0} (@Nat) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (7183 : Nat) (@instOfNatNat (7183 : Nat)))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (837 : Nat)
  (@instOfNatNat (837 : Nat))) _v0)) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3693 : Nat) (@instOfNatNat (3693 :
  Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3696 : Nat) (@instOfNatNat (3696 : Nat))) (@List.nil.{0}
  (@Nat))))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3675 : Nat) (@instOfNatNat (3675 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3678 : Nat) (@instOfNatNat (3678 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3690 : Nat) (@instOfNatNat (3690 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3693 : Nat) (@instOfNatNat
  (3693 : Nat))) _v1)))));
(let _v2 : (@List.{0} (@Nat)) := (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3672 : Nat) (@instOfNatNat (3672 :
  Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3675 : Nat) (@instOfNatNat (3675 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3678 : Nat) (@instOfNatNat (3678 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3682 : Nat) (@instOfNatNat (3682 : Nat))) _v1))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3660 : Nat) (@instOfNatNat (3660 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3664 : Nat) (@instOfNatNat (3664 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3657 : Nat) (@instOfNatNat (3657 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3660 : Nat) (@instOfNatNat
  (3660 : Nat))) _v2))))));
(let _v2 : (@List.{0} (@Nat)) := (let _v2 : (@List.{0} (@Nat)) := (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3639
  : Nat) (@instOfNatNat (3639 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3642 : Nat) (@instOfNatNat (3642 :
  Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3654 : Nat) (@instOfNatNat (3654 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3657 : Nat) (@instOfNatNat (3657 : Nat))) _v1))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3636 : Nat) (@instOfNatNat (3636 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3639 : Nat) (@instOfNatNat (3639 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3642 : Nat) (@instOfNatNat (3642 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3646 : Nat) (@instOfNatNat
  (3646 : Nat))) _v2)))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3606 : Nat) (@instOfNatNat (3606 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3618 : Nat) (@instOfNatNat (3618 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3621 : Nat) (@instOfNatNat (3621 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3624 : Nat) (@instOfNatNat
  (3624 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3700 : Nat) (@instOfNatNat (3700 : Nat)))
  (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3621 : Nat) (@instOfNatNat (3621 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3624 : Nat) (@instOfNatNat (3624 : Nat))) _v2)))))))));
(let _v2 : (@List.{0} (@Nat)) := (let _v2 : (@List.{0} (@Nat)) := (let _v2 : (@List.{0} (@Nat)) := (@List.cons.{0}
  (@Nat) (@OfNat.ofNat.{0} (@Nat) (3603 : Nat) (@instOfNatNat (3603 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0}
  (@Nat) (3606 : Nat) (@instOfNatNat (3606 : Nat))) (@List.cons.{0} (@Nat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (7183 : Nat) (@instOfNatNat (7183 : Nat))) (@HMul.hMul.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (837 : Nat) (@instOfNatNat (837
  : Nat))) _v0)) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3603 : Nat) (@instOfNatNat (3603 : Nat))) _v1))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3592 : Nat) (@instOfNatNat (3592 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3585 : Nat) (@instOfNatNat (3585 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3588 : Nat) (@instOfNatNat (3588 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3600 : Nat) (@instOfNatNat
  (3600 : Nat))) _v2)))));
(let _v3 : (@List.{0} (@Nat)) := (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3570 : Nat) (@instOfNatNat (3570 :
  Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3582 : Nat) (@instOfNatNat (3582 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3585 : Nat) (@instOfNatNat (3585 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3588 : Nat) (@instOfNatNat (3588 : Nat))) _v2))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3567 : Nat) (@instOfNatNat (3567 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3570 : Nat) (@instOfNatNat (3570 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3574 : Nat) (@instOfNatNat (3574 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3567 : Nat) (@instOfNatNat
  (3567 : Nat))) _v3))))));
(let _v3 : (@List.{0} (@Nat)) := (let _v3 : (@List.{0} (@Nat)) := (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3448
  : Nat) (@instOfNatNat (3448 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3551 : Nat) (@instOfNatNat (3551 :
  Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3554 : Nat) (@instOfNatNat (3554 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3564 : Nat) (@instOfNatNat (3564 : Nat))) _v2))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3534 : Nat) (@instOfNatNat (3534 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3548 : Nat) (@instOfNatNat (3548 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3551 : Nat) (@instOfNatNat (3551 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3554 : Nat) (@instOfNatNat
  (3554 : Nat))) _v3)))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3525 : Nat) (@instOfNatNat (3525 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3518 : Nat) (@instOfNatNat (3518 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3538 : Nat) (@instOfNatNat (3538 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3522 : Nat) (@instOfNatNat
  (3522 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3525 : Nat) (@instOfNatNat (3525 : Nat)))
  (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3556 : Nat) (@instOfNatNat (3556 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3531 : Nat) (@instOfNatNat (3531 : Nat))) _v3))))))))));
(let _v2 : (@List.{0} (@Nat)) := (let _v2 : (@List.{0} (@Nat)) := (let _v2 : (@List.{0} (@Nat)) := (let _v2 : (@List.{0}
  (@Nat)) := (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3512 : Nat) (@instOfNatNat (3512 : Nat))) (@List.cons.{0}
  (@Nat) (@OfNat.ofNat.{0} (@Nat) (3515 : Nat) (@instOfNatNat (3515 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0}
  (@Nat) (3518 : Nat) (@instOfNatNat (3518 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3528 : Nat)
  (@instOfNatNat (3528 : Nat))) _v1))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3498 : Nat) (@instOfNatNat (3498 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3502 : Nat) (@instOfNatNat (3502 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3495 : Nat) (@instOfNatNat (3495 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3498 : Nat) (@instOfNatNat
  (3498 : Nat))) _v2)))));
(let _v3 : (@List.{0} (@Nat)) := (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3477 : Nat) (@instOfNatNat (3477 :
  Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3480 : Nat) (@instOfNatNat (3480 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3492 : Nat) (@instOfNatNat (3492 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3495 : Nat) (@instOfNatNat (3495 : Nat))) _v2))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3610 : Nat) (@instOfNatNat (3610 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (364 : Nat) (@instOfNatNat (364 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3477
  : Nat) (@instOfNatNat (3477 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3484 : Nat) (@instOfNatNat (3484 :
  Nat))) _v3))))));
(let _v3 : (@List.{0} (@Nat)) := (let _v3 : (@List.{0} (@Nat)) := (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3464
  : Nat) (@instOfNatNat (3464 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3465 : Nat) (@instOfNatNat (3465 :
  Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3468 : Nat) (@instOfNatNat (3468 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3464 : Nat) (@instOfNatNat (3464 : Nat))) _v2))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3443 : Nat) (@instOfNatNat (3443 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3446 : Nat) (@instOfNatNat (3446 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3458 : Nat) (@instOfNatNat (3458 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3461 : Nat) (@instOfNatNat
  (3461 : Nat))) _v3)))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (2962 : Nat) (@instOfNatNat (2962 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3425 : Nat) (@instOfNatNat (3425 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3428 : Nat) (@instOfNatNat (3428 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3440 : Nat) (@instOfNatNat
  (3440 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3443 : Nat) (@instOfNatNat (3443 : Nat)))
  (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3446 : Nat) (@instOfNatNat (3446 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3448 : Nat) (@instOfNatNat (3448 : Nat))) _v3)))))))));
(let _v3 : (@List.{0} (@Nat)) := (let _v3 : (@List.{0} (@Nat)) := (let _v3 : (@List.{0} (@Nat)) := (@List.cons.{0}
  (@Nat) (@OfNat.ofNat.{0} (@Nat) (3410 : Nat) (@instOfNatNat (3410 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0}
  (@Nat) (3422 : Nat) (@instOfNatNat (3422 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3425 : Nat)
  (@instOfNatNat (3425 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3428 : Nat) (@instOfNatNat (3428 : Nat)))
  _v2))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3407 : Nat) (@instOfNatNat (3407 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3410 : Nat) (@instOfNatNat (3410 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3412 : Nat) (@instOfNatNat (3412 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3407 : Nat) (@instOfNatNat
  (3407 : Nat))) _v3)))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3386 : Nat) (@instOfNatNat (3386 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3389 : Nat) (@instOfNatNat (3389 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3392 : Nat) (@instOfNatNat (3392 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3394 : Nat) (@instOfNatNat
  (3394 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3389 : Nat) (@instOfNatNat (3389 : Nat)))
  (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3392 : Nat) (@instOfNatNat (3392 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3404 : Nat) (@instOfNatNat (3404 : Nat))) _v3))))))));
(let _v4 : (@List.{0} (@Nat)) := (let _v4 : (@List.{0} (@Nat)) := (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3374
  : Nat) (@instOfNatNat (3374 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3368 : Nat) (@instOfNatNat (3368 :
  Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3380 : Nat) (@instOfNatNat (3380 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3374 : Nat) (@instOfNatNat (3374 : Nat))) _v3))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3353 : Nat) (@instOfNatNat (3353 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3353 : Nat) (@instOfNatNat (3353 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3368 : Nat) (@instOfNatNat (3368 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3371 : Nat) (@instOfNatNat
  (3371 : Nat))) _v4)))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3330 : Nat) (@instOfNatNat (3330 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (364 : Nat) (@instOfNatNat (364 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3345
  : Nat) (@instOfNatNat (3345 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3088 : Nat) (@instOfNatNat (3088 :
  Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (364 : Nat) (@instOfNatNat (364 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3345 : Nat) (@instOfNatNat (3345 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3358 : Nat) (@instOfNatNat (3358 : Nat))) _v4)))))))))))))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3306 : Nat) (@instOfNatNat (3306 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3309 : Nat) (@instOfNatNat (3309 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3321 : Nat) (@instOfNatNat (3321 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3324 : Nat) (@instOfNatNat
  (3324 : Nat))) _v1)))));
(let _v2 : (@List.{0} (@Nat)) := (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3303 : Nat) (@instOfNatNat (3303 :
  Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3306 : Nat) (@instOfNatNat (3306 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3309 : Nat) (@instOfNatNat (3309 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3313 : Nat) (@instOfNatNat (3313 : Nat))) _v1))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3291 : Nat) (@instOfNatNat (3291 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3295 : Nat) (@instOfNatNat (3295 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3288 : Nat) (@instOfNatNat (3288 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3291 : Nat) (@instOfNatNat
  (3291 : Nat))) _v2))))));
(let _v2 : (@List.{0} (@Nat)) := (let _v2 : (@List.{0} (@Nat)) := (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3270
  : Nat) (@instOfNatNat (3270 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3273 : Nat) (@instOfNatNat (3273 :
  Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3285 : Nat) (@instOfNatNat (3285 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3288 : Nat) (@instOfNatNat (3288 : Nat))) _v1))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3267 : Nat) (@instOfNatNat (3267 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3270 : Nat) (@instOfNatNat (3270 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3273 : Nat) (@instOfNatNat (3273 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3277 : Nat) (@instOfNatNat
  (3277 : Nat))) _v2)))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3237 : Nat) (@instOfNatNat (3237 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3249 : Nat) (@instOfNatNat (3249 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3252 : Nat) (@instOfNatNat (3252 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3255 : Nat) (@instOfNatNat
  (3255 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3259 : Nat) (@instOfNatNat (3259 : Nat)))
  (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3252 : Nat) (@instOfNatNat (3252 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3255 : Nat) (@instOfNatNat (3255 : Nat))) _v2)))))))));
(let _v2 : (@List.{0} (@Nat)) := (let _v2 : (@List.{0} (@Nat)) := (let _v2 : (@List.{0} (@Nat)) := (@List.cons.{0}
  (@Nat) (@OfNat.ofNat.{0} (@Nat) (3225 : Nat) (@instOfNatNat (3225 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0}
  (@Nat) (3228 : Nat) (@instOfNatNat (3228 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3628 : Nat)
  (@instOfNatNat (3628 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3234 : Nat) (@instOfNatNat (3234 : Nat)))
  _v1))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3231 : Nat) (@instOfNatNat (3231 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3228 : Nat) (@instOfNatNat (3228 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3221 : Nat) (@instOfNatNat (3221 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3241 : Nat) (@instOfNatNat
  (3241 : Nat))) _v2)))));
(let _v3 : (@List.{0} (@Nat)) := (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3203 : Nat) (@instOfNatNat (3203 :
  Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3215 : Nat) (@instOfNatNat (3215 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3218 : Nat) (@instOfNatNat (3218 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3221 : Nat) (@instOfNatNat (3221 : Nat))) _v2))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3200 : Nat) (@instOfNatNat (3200 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3203 : Nat) (@instOfNatNat (3203 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3205 : Nat) (@instOfNatNat (3205 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3200 : Nat) (@instOfNatNat
  (3200 : Nat))) _v3))))));
(let _v3 : (@List.{0} (@Nat)) := (let _v3 : (@List.{0} (@Nat)) := (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3187
  : Nat) (@instOfNatNat (3187 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3182 : Nat) (@instOfNatNat (3182 :
  Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3185 : Nat) (@instOfNatNat (3185 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3197 : Nat) (@instOfNatNat (3197 : Nat))) _v2))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3167 : Nat) (@instOfNatNat (3167 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3179 : Nat) (@instOfNatNat (3179 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3182 : Nat) (@instOfNatNat (3182 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3185 : Nat) (@instOfNatNat
  (3185 : Nat))) _v3)))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3146 : Nat) (@instOfNatNat (3146 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3149 : Nat) (@instOfNatNat (3149 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3161 : Nat) (@instOfNatNat (3161 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3164 : Nat) (@instOfNatNat
  (3164 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3167 : Nat) (@instOfNatNat (3167 : Nat)))
  (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3169 : Nat) (@instOfNatNat (3169 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3164 : Nat) (@instOfNatNat (3164 : Nat))) _v3))))))))))))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3131 : Nat) (@instOfNatNat (3131 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3125 : Nat) (@instOfNatNat (3125 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3137 : Nat) (@instOfNatNat (3137 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3131 : Nat) (@instOfNatNat
  (3131 : Nat))) _v1)))));
(let _v2 : (@List.{0} (@Nat)) := (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3110 : Nat) (@instOfNatNat (3110 :
  Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3113 : Nat) (@instOfNatNat (3113 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3125 : Nat) (@instOfNatNat (3125 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3128 : Nat) (@instOfNatNat (3128 : Nat))) _v1))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3350 : Nat) (@instOfNatNat (3350 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3113 : Nat) (@instOfNatNat (3113 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3102 : Nat) (@instOfNatNat (3102 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3115 : Nat) (@instOfNatNat
  (3115 : Nat))) _v2))))));
(let _v2 : (@List.{0} (@Nat)) := (let _v2 : (@List.{0} (@Nat)) := (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3084
  : Nat) (@instOfNatNat (3084 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3096 : Nat) (@instOfNatNat (3096 :
  Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3099 : Nat) (@instOfNatNat (3099 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3102 : Nat) (@instOfNatNat (3102 : Nat))) _v1))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (364 : Nat) (@instOfNatNat (364 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3084 : Nat) (@instOfNatNat (3084 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3088 : Nat) (@instOfNatNat (3088 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (364 : Nat) (@instOfNatNat
  (364 : Nat))) _v2)))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3060 : Nat) (@instOfNatNat (3060 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3063 : Nat) (@instOfNatNat (3063 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3066 : Nat) (@instOfNatNat (3066 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (361 : Nat) (@instOfNatNat
  (361 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3072 : Nat) (@instOfNatNat (3072 : Nat))) (@List.cons.{0}
  (@Nat) (@OfNat.ofNat.{0} (@Nat) (367 : Nat) (@instOfNatNat (367 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3069 : Nat) (@instOfNatNat (3069 : Nat))) _v2)))))))))))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3027 : Nat) (@instOfNatNat (3027 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3030 : Nat) (@instOfNatNat (3030 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3042 : Nat) (@instOfNatNat (3042 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3045 : Nat) (@instOfNatNat
  (3045 : Nat))) _v1)))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3016 : Nat) (@instOfNatNat (3016 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3009 : Nat) (@instOfNatNat (3009 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3012 : Nat) (@instOfNatNat (3012 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3024 : Nat) (@instOfNatNat
  (3024 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3027 : Nat) (@instOfNatNat (3027 : Nat)))
  (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3030 : Nat) (@instOfNatNat (3030 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3034 : Nat) (@instOfNatNat (3034 : Nat))) _v1))))))))))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (364 : Nat) (@instOfNatNat (364 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (2991 : Nat) (@instOfNatNat (2991 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (2998 : Nat) (@instOfNatNat (2998 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (2991 : Nat) (@instOfNatNat
  (2991 : Nat))) _v1)))))))))))))) := by
  exact @CappedWeight.instructions.eq_1

-- Independent literal expected type for CappedWorkspace.Target.Raw.
noncomputable def PartACanonical.Types.p0261 :
(∀ (_v0 : (@Nat)),
(Sort 0)) := by
  exact @CappedWorkspace.Target.Raw

-- Independent literal expected type for CappedWorkspace.Target.deadline.
noncomputable def PartACanonical.Types.p0262 :
(∀ (_v0 : (@Nat)),
(@Nat)) := by
  exact @CappedWorkspace.Target.deadline

-- Independent literal expected type for CappedWorkspace.Target.image.
noncomputable def PartACanonical.Types.p0263 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(@Option.{0} (@Bool)))))))) := by
  exact @CappedWorkspace.Target.image

-- Independent literal expected type for CappedWorkspace.Target.image.eq_1.
noncomputable def PartACanonical.Types.p0264 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@CappedWorkspace.Target.image _v0 _v1 _v2 _v3 _v4 _v5) (@ite.{(0 + 1)}
  (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v1 _v5) (@LT.lt.{0} (@Nat) (@instLTNat) _v5 (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))
  (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) _v1 _v5) (@LT.lt.{0} (@Nat) (@instLTNat) _v5 (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Nat.decLt _v1 _v5)
  (@Nat.decLt _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))))) (@Option.some.{0} (@Bool) (@Bool.true)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Or (@And (@LT.lt.{0} (@Nat)
  (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2
  : Nat)))) _v5) (@LT.lt.{0} (@Nat) (@instLTNat) _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) _v2) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))))) (@Or (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) _v2) (@OfNat.ofNat.{0} (@Nat)
  (3 : Nat) (@instOfNatNat (3 : Nat)))) _v5) (@LT.lt.{0} (@Nat) (@instLTNat) _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@Or (@And (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))
  _v5) (@LT.lt.{0} (@Nat) (@instLTNat) _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (5 :
  Nat) (@instOfNatNat (5 : Nat)))))) (@Or (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v4)) _v2)
  (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) _v5) (@LT.lt.{0} (@Nat) (@instLTNat) _v5 (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))) (@And (@LT.lt.{0}
  (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (6 : Nat)
  (@instOfNatNat (6 : Nat)))) _v5) (@LT.lt.{0} (@Nat) (@instLTNat) _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v4)) _v2)
  (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))))))))) (@instDecidableOr (@And (@LT.lt.{0} (@Nat)
  (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2
  : Nat)))) _v5) (@LT.lt.{0} (@Nat) (@instLTNat) _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) _v2) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))))) (@Or (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) _v2) (@OfNat.ofNat.{0} (@Nat)
  (3 : Nat) (@instOfNatNat (3 : Nat)))) _v5) (@LT.lt.{0} (@Nat) (@instLTNat) _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@Or (@And (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))
  _v5) (@LT.lt.{0} (@Nat) (@instLTNat) _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (5 :
  Nat) (@instOfNatNat (5 : Nat)))))) (@Or (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v4)) _v2)
  (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) _v5) (@LT.lt.{0} (@Nat) (@instLTNat) _v5 (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))) (@And (@LT.lt.{0}
  (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (6 : Nat)
  (@instOfNatNat (6 : Nat)))) _v5) (@LT.lt.{0} (@Nat) (@instLTNat) _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v4)) _v2)
  (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v5)
  (@LT.lt.{0} (@Nat) (@instLTNat) _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) _v2) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 :
  Nat))))) (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat)))) _v5) (@Nat.decLt _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) _v2) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 :
  Nat)))))) (@instDecidableOr (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) _v2) (@OfNat.ofNat.{0} (@Nat)
  (3 : Nat) (@instOfNatNat (3 : Nat)))) _v5) (@LT.lt.{0} (@Nat) (@instLTNat) _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@Or (@And (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))
  _v5) (@LT.lt.{0} (@Nat) (@instLTNat) _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (5 :
  Nat) (@instOfNatNat (5 : Nat)))))) (@Or (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v4)) _v2)
  (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) _v5) (@LT.lt.{0} (@Nat) (@instLTNat) _v5 (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))) (@And (@LT.lt.{0}
  (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (6 : Nat)
  (@instOfNatNat (6 : Nat)))) _v5) (@LT.lt.{0} (@Nat) (@instLTNat) _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v4)) _v2)
  (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 _v4) _v2) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v5) (@LT.lt.{0} (@Nat)
  (@instLTNat) _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))))) (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) _v2) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))
  _v5) (@Nat.decLt _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))))) (@instDecidableOr (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v5) (@LT.lt.{0} (@Nat) (@instLTNat) _v5
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))))
  (@Or (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat)
  (5 : Nat) (@instOfNatNat (5 : Nat)))) _v5) (@LT.lt.{0} (@Nat) (@instLTNat) _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))
  _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))) (@And (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))
  _v5) (@LT.lt.{0} (@Nat) (@instLTNat) _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (7 :
  Nat) (@instOfNatNat (7 : Nat))))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v5) (@LT.lt.{0} (@Nat) (@instLTNat) _v5
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))
  (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))
  _v5) (@Nat.decLt _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (5 : Nat)
  (@instOfNatNat (5 : Nat)))))) (@instDecidableOr (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))
  _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) _v5) (@LT.lt.{0} (@Nat) (@instLTNat) _v5
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))))
  (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (6 :
  Nat) (@instOfNatNat (6 : Nat)))) _v5) (@LT.lt.{0} (@Nat) (@instLTNat) _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v4)) _v2)
  (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))
  _v5) (@LT.lt.{0} (@Nat) (@instLTNat) _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (6 :
  Nat) (@instOfNatNat (6 : Nat))))) (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat)
  (5 : Nat) (@instOfNatNat (5 : Nat)))) _v5) (@Nat.decLt _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v4)) _v2)
  (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))
  _v5) (@LT.lt.{0} (@Nat) (@instLTNat) _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (7 :
  Nat) (@instOfNatNat (7 : Nat))))) (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat)
  (6 : Nat) (@instOfNatNat (6 : Nat)))) _v5) (@Nat.decLt _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v4)) _v2)
  (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))))))))) (@Option.some.{0} (@Bool) (@Bool.false)) (@_v0
  _v5)))))))))) := by
  exact @CappedWorkspace.Target.image.eq_1

-- Complete literal proposition for CappedWorkspace.Target.image.eq_1; original proof reused.
theorem PartACanonical.Surface.m0166 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@CappedWorkspace.Target.image _v0 _v1 _v2 _v3 _v4 _v5) (@ite.{(0 + 1)}
  (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v1 _v5) (@LT.lt.{0} (@Nat) (@instLTNat) _v5 (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))
  (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) _v1 _v5) (@LT.lt.{0} (@Nat) (@instLTNat) _v5 (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Nat.decLt _v1 _v5)
  (@Nat.decLt _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))))) (@Option.some.{0} (@Bool) (@Bool.true)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Or (@And (@LT.lt.{0} (@Nat)
  (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2
  : Nat)))) _v5) (@LT.lt.{0} (@Nat) (@instLTNat) _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) _v2) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))))) (@Or (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) _v2) (@OfNat.ofNat.{0} (@Nat)
  (3 : Nat) (@instOfNatNat (3 : Nat)))) _v5) (@LT.lt.{0} (@Nat) (@instLTNat) _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@Or (@And (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))
  _v5) (@LT.lt.{0} (@Nat) (@instLTNat) _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (5 :
  Nat) (@instOfNatNat (5 : Nat)))))) (@Or (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v4)) _v2)
  (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) _v5) (@LT.lt.{0} (@Nat) (@instLTNat) _v5 (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))) (@And (@LT.lt.{0}
  (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (6 : Nat)
  (@instOfNatNat (6 : Nat)))) _v5) (@LT.lt.{0} (@Nat) (@instLTNat) _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v4)) _v2)
  (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))))))))) (@instDecidableOr (@And (@LT.lt.{0} (@Nat)
  (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2
  : Nat)))) _v5) (@LT.lt.{0} (@Nat) (@instLTNat) _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) _v2) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))))) (@Or (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) _v2) (@OfNat.ofNat.{0} (@Nat)
  (3 : Nat) (@instOfNatNat (3 : Nat)))) _v5) (@LT.lt.{0} (@Nat) (@instLTNat) _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@Or (@And (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))
  _v5) (@LT.lt.{0} (@Nat) (@instLTNat) _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (5 :
  Nat) (@instOfNatNat (5 : Nat)))))) (@Or (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v4)) _v2)
  (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) _v5) (@LT.lt.{0} (@Nat) (@instLTNat) _v5 (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))) (@And (@LT.lt.{0}
  (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (6 : Nat)
  (@instOfNatNat (6 : Nat)))) _v5) (@LT.lt.{0} (@Nat) (@instLTNat) _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v4)) _v2)
  (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v5)
  (@LT.lt.{0} (@Nat) (@instLTNat) _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) _v2) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 :
  Nat))))) (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat)))) _v5) (@Nat.decLt _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) _v2) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 :
  Nat)))))) (@instDecidableOr (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) _v2) (@OfNat.ofNat.{0} (@Nat)
  (3 : Nat) (@instOfNatNat (3 : Nat)))) _v5) (@LT.lt.{0} (@Nat) (@instLTNat) _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@Or (@And (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))
  _v5) (@LT.lt.{0} (@Nat) (@instLTNat) _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (5 :
  Nat) (@instOfNatNat (5 : Nat)))))) (@Or (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v4)) _v2)
  (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) _v5) (@LT.lt.{0} (@Nat) (@instLTNat) _v5 (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))) (@And (@LT.lt.{0}
  (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (6 : Nat)
  (@instOfNatNat (6 : Nat)))) _v5) (@LT.lt.{0} (@Nat) (@instLTNat) _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v4)) _v2)
  (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 _v4) _v2) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v5) (@LT.lt.{0} (@Nat)
  (@instLTNat) _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))))) (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) _v2) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))
  _v5) (@Nat.decLt _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))))) (@instDecidableOr (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v5) (@LT.lt.{0} (@Nat) (@instLTNat) _v5
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))))
  (@Or (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat)
  (5 : Nat) (@instOfNatNat (5 : Nat)))) _v5) (@LT.lt.{0} (@Nat) (@instLTNat) _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))
  _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))) (@And (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))
  _v5) (@LT.lt.{0} (@Nat) (@instLTNat) _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (7 :
  Nat) (@instOfNatNat (7 : Nat))))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v5) (@LT.lt.{0} (@Nat) (@instLTNat) _v5
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))
  (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))
  _v5) (@Nat.decLt _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (5 : Nat)
  (@instOfNatNat (5 : Nat)))))) (@instDecidableOr (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))
  _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) _v5) (@LT.lt.{0} (@Nat) (@instLTNat) _v5
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))))
  (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (6 :
  Nat) (@instOfNatNat (6 : Nat)))) _v5) (@LT.lt.{0} (@Nat) (@instLTNat) _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v4)) _v2)
  (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))
  _v5) (@LT.lt.{0} (@Nat) (@instLTNat) _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (6 :
  Nat) (@instOfNatNat (6 : Nat))))) (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat)
  (5 : Nat) (@instOfNatNat (5 : Nat)))) _v5) (@Nat.decLt _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v4)) _v2)
  (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))
  _v5) (@LT.lt.{0} (@Nat) (@instLTNat) _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (7 :
  Nat) (@instOfNatNat (7 : Nat))))) (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat)
  (6 : Nat) (@instOfNatNat (6 : Nat)))) _v5) (@Nat.decLt _v5 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v4)) _v2)
  (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))))))))) (@Option.some.{0} (@Bool) (@Bool.false)) (@_v0
  _v5)))))))))) := by
  exact @CappedWorkspace.Target.image.eq_1

-- Independent literal expected type for CappedWorkspace.instructions.
noncomputable def PartACanonical.Types.p0265 :
(@List.{0} (@Nat)) := by
  exact @CappedWorkspace.instructions

-- Independent literal expected type for CappedWorkspace.overflow_bits.
noncomputable def PartACanonical.Types.p0266 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@List.{0} (@Bool)) (@Body.iterBits (@List.replicate.{0} (@Bool) _v0 (@Bool.false)) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v0)) (@List.replicate.{0} (@Bool) _v0 (@Bool.false)))) := by
  exact @CappedWorkspace.overflow_bits

-- Complete literal proposition for CappedWorkspace.overflow_bits; original proof reused.
theorem PartACanonical.Surface.m0167 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@List.{0} (@Bool)) (@Body.iterBits (@List.replicate.{0} (@Bool) _v0 (@Bool.false)) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v0)) (@List.replicate.{0} (@Bool) _v0 (@Bool.false)))) := by
  exact @CappedWorkspace.overflow_bits

-- Independent literal expected type for CappedWorkspace.raw_accepted_workspace.
noncomputable def PartACanonical.Types.p0267 :
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
  (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)))) (fun (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v11 (@CappedWorkspace.Target.deadline
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
  (@Cursor.machine _v0) (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (201 : Nat) (@instOfNatNat (201 : Nat)))))))) (let _v13 :
  (∀ (_v13 : (@Nat)),
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
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 _v2) (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v9)) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v15))) _v6)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v15))) _v6)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2))))) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v15))) _v6)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v15))) _v6))) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat
  (7 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
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
  _v2)) (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (201 : Nat) (@instOfNatNat (201 : Nat)))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2))
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v12) (fun (_v15 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@CappedWorkspace.Target.image (@SuffixCap.Target.image _v14 (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos
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
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v9) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat)))) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v16))) _v6))
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
  exact @CappedWorkspace.raw_accepted_workspace

-- Complete literal proposition for CappedWorkspace.raw_accepted_workspace; original proof reused.
theorem PartACanonical.Surface.m0168 :
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
  (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)))) (fun (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v11 (@CappedWorkspace.Target.deadline
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
  (@Cursor.machine _v0) (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (201 : Nat) (@instOfNatNat (201 : Nat)))))))) (let _v13 :
  (∀ (_v13 : (@Nat)),
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
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 _v2) (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v9)) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v15))) _v6)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v15))) _v6)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2))))) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v15))) _v6)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v15 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v15))) _v6))) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat
  (7 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
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
  _v2)) (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (201 : Nat) (@instOfNatNat (201 : Nat)))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2))
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v12) (fun (_v15 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@CappedWorkspace.Target.image (@SuffixCap.Target.image _v14 (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos
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
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v9) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat)))) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v16))) _v6))
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
  exact @CappedWorkspace.raw_accepted_workspace

-- Independent literal expected type for CappedWorkspace.raw_workspace.
noncomputable def PartACanonical.Types.p0268 :
(∀ (_v0 : (@Nat)),
(@CappedWorkspace.Target.Raw _v0)) := by
  exact @CappedWorkspace.raw_workspace

-- Complete literal proposition for CappedWorkspace.raw_workspace; original proof reused.
theorem PartACanonical.Surface.m0169 :
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
  (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)))) (fun (_v15 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v14 (@CappedWorkspace.Target.deadline
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
  (@Cursor.machine _v0) (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (201 : Nat) (@instOfNatNat (201 : Nat)))))))) (let _v16 :
  (∀ (_v16 : (@Nat)),
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
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 _v2) (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v9)) (@HPow.hPow.{0, 0, 0} (@Nat)
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v18))) _v5)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2))))) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v18))) _v5))) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat
  (7 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
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
  _v2)) (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (201 : Nat) (@instOfNatNat (201 : Nat)))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2))
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v15) (fun (_v18 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@CappedWorkspace.Target.image (@SuffixCap.Target.image _v17 (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos
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
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v9) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat)))) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v19))) _v5))
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
  exact @CappedWorkspace.raw_workspace

-- Independent literal expected type for CappedWorkspace.workspace.
noncomputable def PartACanonical.Types.p0270 :
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
(∀ (_v10 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v4)),
(∀ (_v11 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v6)),
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 _v5) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))) _v6) _v7)),
(∀ (_v13 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v9 _v3) (@Option.none.{0} (@Bool)))),
(∀ (_v14 : (∀ (_v14 : (@Nat)),
(∀ (_v15 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v14)),
(∀ (_v16 : (@LT.lt.{0} (@Nat) (@instLTNat) _v14 _v4)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v9 _v14) (@Option.some.{0} (@Bool) (@Bool.false))))))),
(∀ (_v15 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v9 _v4) (@Option.none.{0} (@Bool)))),
(∀ (_v16 : (∀ (_v16 : (@Nat)),
(∀ (_v17 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 _v16)),
(∀ (_v18 : (@LT.lt.{0} (@Nat) (@instLTNat) _v16 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 _v5)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v9 _v16) (@Option.some.{0} (@Bool) (@Bool.false))))))),
(∀ (_v17 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v9 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 _v5)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Option.none.{0} (@Bool)))),
(∀ (_v18 : (∀ (_v18 : (@Nat)),
(∀ (_v19 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 _v5)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v18)),
(∀ (_v20 : (@LE.le.{0} (@Nat) (@instLENat) _v18 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 _v5) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))) _v6))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v9 _v18) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v19 : (∀ (_v19 : (@Nat)),
(∀ (_v20 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 _v5) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))) _v6) _v19)),
(∀ (_v21 : (@LT.lt.{0} (@Nat) (@instLTNat) _v19 _v7)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v9 _v19) (@Option.none.{0} (@Bool))))))),
(∀ (_v20 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v9 _v7) (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v21 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v9 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v7 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Option.none.{0} (@Bool)))),
(∀ (_v22 : (∀ (_v22 : (@Nat)),
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v7 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v22)),
(∀ (_v24 : (@LT.lt.{0} (@Nat) (@instLTNat) _v22 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v7 _v8)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v9 _v22) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v23 : (∀ (_v23 : (@Nat)),
(∀ (_v24 : (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v7 _v8)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v23)),
(∀ (_v25 : (@LE.le.{0} (@Nat) (@instLENat) _v23 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v7 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v8)) _v5) (@OfNat.ofNat.{0} (@Nat)
  (7 : Nat) (@instOfNatNat (7 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v9 _v23) (@Option.none.{0} (@Bool))))))),
(∀ (_v24 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v7 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v8)) _v5) (@OfNat.ofNat.{0} (@Nat)
  (7 : Nat) (@instOfNatNat (7 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))),
(@Exists.{(0 + 1)} (@Nat) (fun (_v25 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v25 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (128 : Nat) (@instOfNatNat (128 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v5 _v8) (@OfNat.ofNat.{0} (@Nat) (1 :
  Nat) (@instOfNatNat (1 : Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v7 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v8)) _v5) (@OfNat.ofNat.{0} (@Nat) (9 :
  Nat) (@instOfNatNat (9 : Nat)))))) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0)) _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Cursor.machine _v0) _v1 _v2 _v25 (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0)) _v1 _v2 (@Cursor.rReady _v0) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) _v3 (@Decidable.byContradiction (@LT.lt.{0} (@Nat) (@instLTNat) _v3
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (@Nat.decLt _v3 (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (fun
  (_v26 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat) _v3 (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)))) =>
(@CappedWorkspace.workspace._proof_1 _v1 _v2 _v3 _v4 _v5 _v6 _v7 _v8 _v10 _v11 _v12 _v24 _v26)))) (fun (_v26 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))) =>
(@_v9 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) _v26))))) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0)) _v1 _v2 (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat)
  (201 : Nat) (@instOfNatNat (201 : Nat)))) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v7 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@Decidable.byContradiction (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v7 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v7 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (fun (_v26 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v7 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)))) =>
(@CappedWorkspace.workspace._proof_2 _v1 _v2 _v3 _v4 _v5 _v6 _v7 _v8 _v24 _v26)))) (fun (_v26 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))) =>
(@CappedWorkspace.Target.image _v9 _v4 _v5 _v7 _v8 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) _v26)))))
  (∀ (_v26 : (@Nat)),
(∀ (_v27 : (@LT.lt.{0} (@Nat) (@instLTNat) _v26 _v25)),
(@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0)) _v1
  _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Cursor.machine _v0) _v1 _v2 _v26 (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0)) _v1 _v2 (@Cursor.rReady _v0) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) _v3 (@Decidable.byContradiction (@LT.lt.{0} (@Nat) (@instLTNat) _v3
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (@Nat.decLt _v3 (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (fun
  (_v28 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat) _v3 (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)))) =>
(@CappedWorkspace.workspace._proof_1 _v1 _v2 _v3 _v4 _v5 _v6 _v7 _v8 _v10 _v11 _v12 _v24 _v28)))) (fun (_v28 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))) =>
(@_v9 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) _v28))))))) (@OfNat.ofNat.{0} (@Nat) (201 : Nat)
  (@instOfNatNat (201 : Nat))))))))))))))))))))))))))))))))))) := by
  exact @CappedWorkspace.workspace

-- Complete literal proposition for CappedWorkspace.workspace; original proof reused.
theorem PartACanonical.Surface.m0171 :
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
(∀ (_v10 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v4)),
(∀ (_v11 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v6)),
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 _v5) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))) _v6) _v7)),
(∀ (_v13 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v9 _v3) (@Option.none.{0} (@Bool)))),
(∀ (_v14 : (∀ (_v14 : (@Nat)),
(∀ (_v15 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v14)),
(∀ (_v16 : (@LT.lt.{0} (@Nat) (@instLTNat) _v14 _v4)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v9 _v14) (@Option.some.{0} (@Bool) (@Bool.false))))))),
(∀ (_v15 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v9 _v4) (@Option.none.{0} (@Bool)))),
(∀ (_v16 : (∀ (_v16 : (@Nat)),
(∀ (_v17 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 _v16)),
(∀ (_v18 : (@LT.lt.{0} (@Nat) (@instLTNat) _v16 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 _v5)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v9 _v16) (@Option.some.{0} (@Bool) (@Bool.false))))))),
(∀ (_v17 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v9 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 _v5)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Option.none.{0} (@Bool)))),
(∀ (_v18 : (∀ (_v18 : (@Nat)),
(∀ (_v19 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 _v5)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v18)),
(∀ (_v20 : (@LE.le.{0} (@Nat) (@instLENat) _v18 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 _v5) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))) _v6))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v9 _v18) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v19 : (∀ (_v19 : (@Nat)),
(∀ (_v20 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 _v5) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))) _v6) _v19)),
(∀ (_v21 : (@LT.lt.{0} (@Nat) (@instLTNat) _v19 _v7)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v9 _v19) (@Option.none.{0} (@Bool))))))),
(∀ (_v20 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v9 _v7) (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v21 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v9 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v7 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Option.none.{0} (@Bool)))),
(∀ (_v22 : (∀ (_v22 : (@Nat)),
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v7 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v22)),
(∀ (_v24 : (@LT.lt.{0} (@Nat) (@instLTNat) _v22 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v7 _v8)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v9 _v22) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v23 : (∀ (_v23 : (@Nat)),
(∀ (_v24 : (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v7 _v8)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v23)),
(∀ (_v25 : (@LE.le.{0} (@Nat) (@instLENat) _v23 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v7 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v8)) _v5) (@OfNat.ofNat.{0} (@Nat)
  (7 : Nat) (@instOfNatNat (7 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v9 _v23) (@Option.none.{0} (@Bool))))))),
(∀ (_v24 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v7 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v8)) _v5) (@OfNat.ofNat.{0} (@Nat)
  (7 : Nat) (@instOfNatNat (7 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))),
(@Exists.{(0 + 1)} (@Nat) (fun (_v25 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v25 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (128 : Nat) (@instOfNatNat (128 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v5 _v8) (@OfNat.ofNat.{0} (@Nat) (1 :
  Nat) (@instOfNatNat (1 : Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v7 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v8)) _v5) (@OfNat.ofNat.{0} (@Nat) (9 :
  Nat) (@instOfNatNat (9 : Nat)))))) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0)) _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Cursor.machine _v0) _v1 _v2 _v25 (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0)) _v1 _v2 (@Cursor.rReady _v0) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) _v3 (@Decidable.byContradiction (@LT.lt.{0} (@Nat) (@instLTNat) _v3
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (@Nat.decLt _v3 (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (fun
  (_v26 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat) _v3 (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)))) =>
(@CappedWorkspace.workspace._proof_1 _v1 _v2 _v3 _v4 _v5 _v6 _v7 _v8 _v10 _v11 _v12 _v24 _v26)))) (fun (_v26 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))) =>
(@_v9 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) _v26))))) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0)) _v1 _v2 (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat)
  (201 : Nat) (@instOfNatNat (201 : Nat)))) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v7 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@Decidable.byContradiction (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v7 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v7 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (fun (_v26 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v7 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)))) =>
(@CappedWorkspace.workspace._proof_2 _v1 _v2 _v3 _v4 _v5 _v6 _v7 _v8 _v24 _v26)))) (fun (_v26 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))) =>
(@CappedWorkspace.Target.image _v9 _v4 _v5 _v7 _v8 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) _v26)))))
  (∀ (_v26 : (@Nat)),
(∀ (_v27 : (@LT.lt.{0} (@Nat) (@instLTNat) _v26 _v25)),
(@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0)) _v1
  _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Cursor.machine _v0) _v1 _v2 _v26 (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0)) _v1 _v2 (@Cursor.rReady _v0) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) _v3 (@Decidable.byContradiction (@LT.lt.{0} (@Nat) (@instLTNat) _v3
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (@Nat.decLt _v3 (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (fun
  (_v28 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat) _v3 (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)))) =>
(@CappedWorkspace.workspace._proof_1 _v1 _v2 _v3 _v4 _v5 _v6 _v7 _v8 _v10 _v11 _v12 _v24 _v28)))) (fun (_v28 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))) =>
(@_v9 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) _v28))))))) (@OfNat.ofNat.{0} (@Nat) (201 : Nat)
  (@instOfNatNat (201 : Nat))))))))))))))))))))))))))))))))))) := by
  exact @CappedWorkspace.workspace

-- Independent literal expected type for CarryReadyCompletion.body.
noncomputable def PartACanonical.Types.p0271 :
(∀ (_v0 : (@Nat)),
(@CarryWindow.Target.Body _v0)) := by
  exact @CarryReadyCompletion.body

-- Complete literal proposition for CarryReadyCompletion.body; original proof reused.
theorem PartACanonical.Surface.m0172 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Nat)),
(∀ (_v8 : (@Nat)),
(∀ (_v9 : (∀ (_v9 : (@Fin _v4)),
(@Bool))),
(∀ (_v10 : (∀ (_v10 : (@Nat)),
(@Option.{0} (@Bool)))),
(let _v11 : (∀ (_v11 : (@Nat)),
(@Nat)) := (fun (_v11 : (@Nat)) =>
(@CarryWindow.Target.Body.match_1.{(0 + 1)} (fun (_v12 : (@Nat)) =>
(@Nat)) _v11 (fun (_v12 : (@Unit)) =>
(@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v5 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (fun (_v12 : (@Unit)) =>
(@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v5 _v6) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))
  (fun (_v12 : (@Unit)) =>
(@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v5 _v6) _v4) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))) (fun (_v12 : (@Unit)) =>
(@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v5 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v6)) _v4) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))
  (fun (_v12 : (@Unit)) =>
(@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v5 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v6)) _v4) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))
  (fun (_v12 : (@Unit)) =>
(@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v5 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v6)) _v4) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))
  (fun (_v12 : (@Nat)) =>
(@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v5 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v6)) _v4) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 :
  Nat)))))));
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v5)),
(∀ (_v13 : (@LE.le.{0} (@Nat) (@instLENat) _v7 _v6)),
(∀ (_v14 : (@LE.le.{0} (@Nat) (@instLENat) _v8 _v6)),
(∀ (_v15 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 _v3) (@Option.none.{0} (@Bool)))),
(∀ (_v16 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Option.none.{0} (@Bool)))),
(∀ (_v17 : (∀ (_v17 : (@Fin _v4)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v3 _v4) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat)
  (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Fin.val _v4 _v17))) (@Option.some.{0} (@Bool) (@_v9 _v17))))),
(∀ (_v18 : (∀ (_v18 : (@Nat)),
(∀ (_v19 : (@LE.le.{0} (@Nat) (@instLENat) _v18 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 (@_v11 _v18)) (@Option.none.{0} (@Bool)))))),
(∀ (_v19 : (∀ (_v19 : (@Nat)),
(∀ (_v20 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v11 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v19)),
(∀ (_v21 : (@LT.lt.{0} (@Nat) (@instLTNat) _v19 (@_v11 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 _v19) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v20 : (∀ (_v20 : (@Nat)),
(∀ (_v21 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v11 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v20)),
(∀ (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat) _v20 (@_v11 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))),
(@Exists.{(0 + 1)} (@Bool) (fun (_v23 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 _v20) (@Option.some.{0} (@Bool) _v23)))))))),
(∀ (_v21 : (∀ (_v21 : (@Nat)),
(∀ (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v11 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v21)),
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) _v21 (@_v11 (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 _v21) (@Option.some.{0} (@Bool) (@Bool.false))))))),
(∀ (_v22 : (∀ (_v22 : (@Nat)),
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v11 (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v22)),
(∀ (_v24 : (@LT.lt.{0} (@Nat) (@instLTNat) _v22 (@_v11 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 _v22) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat)
  (@instLENat) _v22 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v11
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v7)) (@Nat.decLe _v22 (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v11 (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))
  _v7))))))))),
(∀ (_v23 : (∀ (_v23 : (@Nat)),
(∀ (_v24 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v11 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v23)),
(∀ (_v25 : (@LT.lt.{0} (@Nat) (@instLTNat) _v23 (@_v11 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 _v23) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat)
  (@instLENat) _v23 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v11
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v8)) (@Nat.decLe _v23 (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v11 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))
  _v8))))))))),
(∀ (_v24 : (∀ (_v24 : (@Nat)),
(∀ (_v25 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v11 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) _v24)),
(∀ (_v26 : (@LT.lt.{0} (@Nat) (@instLTNat) _v24 (@_v11 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 _v24) (@Option.some.{0} (@Bool) (@Bool.false))))))),
(∀ (_v25 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v11 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))),
(let _v26 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine
  _v0)) _v1 _v2) := (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@CarryWindow.machine _v0)) _v1 _v2 (@CarryWindow.embed _v0 (@VirtualLeaf.embed _v0
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@IngressRepair.producer) (@Cursor.machine _v0) (@Cursor.q _v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (430 : Nat)
  (@instOfNatNat (430 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (93 : Nat) (@instOfNatNat (93 : Nat))) _v0)))))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@_v11 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))
  (@CarryWindow.Target.Body._proof_1 _v1 _v2 _v4 _v5 _v6 _v25)) (fun (_v26 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v1 _v2))) =>
(@_v10 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) _v26))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v27 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v27 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (8192 : Nat) (@instOfNatNat (8192 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v11 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat)))))) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@CarryWindow.machine _v0)) _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CarryWindow.machine _v0) _v1 _v2 _v27
  _v26) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine
  _v0)) _v1 _v2 (@CarryWindow.ready _v0) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@_v11
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@CarryWindow.Target.Body._proof_2 _v1 _v2 _v4 _v5 _v6
  _v25)) (fun (_v28 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))) =>
(@CarryWindow.Target.image _v10 _v5 _v6 _v4 _v7 (@Pnp4.Frontier.ContractExpansion.bitLength _v8) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v8 (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) _v28))))) (@And (∀ (_v28 : (@Nat)),
(∀ (_v29 : (@LE.le.{0} (@Nat) (@instLENat) _v28 _v27)),
(@And (@LE.le.{0} (@Nat) (@instLENat) (@_v11 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)) _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CarryWindow.machine _v0) _v1 _v2 _v28 _v26)))) (@LE.le.{0} (@Nat)
  (@instLENat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)) _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CarryWindow.machine _v0) _v1 _v2 _v28 _v26))) (@_v11 (@OfNat.ofNat.{0}
  (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))))) (@And (∀ (_v28 : (@Nat)),
(∀ (_v29 : (@LE.le.{0} (@Nat) (@instLENat) _v28 _v27)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))
  _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CarryWindow.machine _v0) _v1 _v2 _v28 _v26))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@CarryWindow.machine _v0))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)) _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CarryWindow.machine _v0) _v1 _v2 _v28 _v26))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@CarryWindow.machine _v0)))))) (∀ (_v28 : (@Nat)),
(∀ (_v29 : (@LT.lt.{0} (@Nat) (@instLTNat) _v28 _v27)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))
  _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CarryWindow.machine _v0) _v1 _v2 _v28 _v26)) (@CarryWindow.ready
  _v0))))))))))))))))))))))))))))))))))))) := by
  exact @CarryReadyCompletion.body

-- Independent literal expected type for CarryReadyCompletion.check_body.
noncomputable def PartACanonical.Types.p0272 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Nat)),
(∀ (_v8 : (@Nat)),
(∀ (_v9 : (∀ (_v9 : (@Fin _v4)),
(@Bool))),
(∀ (_v10 : (∀ (_v10 : (@Nat)),
(@Option.{0} (@Bool)))),
(let _v11 : (∀ (_v11 : (@Nat)),
(@Nat)) := (fun (_v11 : (@Nat)) =>
(@CarryReadyCompletion.check_body.match_1.{(0 + 1)} (fun (_v12 : (@Nat)) =>
(@Nat)) _v11 (fun (_v12 : (@Unit)) =>
(@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v5 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (fun (_v12 : (@Unit)) =>
(@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v5 _v6) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))
  (fun (_v12 : (@Unit)) =>
(@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v5 _v6) _v4) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))) (fun (_v12 : (@Unit)) =>
(@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v5 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v6)) _v4) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))
  (fun (_v12 : (@Unit)) =>
(@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v5 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v6)) _v4) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))
  (fun (_v12 : (@Unit)) =>
(@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v5 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v6)) _v4) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))
  (fun (_v12 : (@Nat)) =>
(@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v5 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v6)) _v4) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 :
  Nat)))))));
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v5)),
(∀ (_v13 : (@LE.le.{0} (@Nat) (@instLENat) _v7 _v6)),
(∀ (_v14 : (@LE.le.{0} (@Nat) (@instLENat) _v8 _v6)),
(∀ (_v15 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 _v3) (@Option.none.{0} (@Bool)))),
(∀ (_v16 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Option.none.{0} (@Bool)))),
(∀ (_v17 : (∀ (_v17 : (@Fin _v4)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v3 _v4) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat)
  (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Fin.val _v4 _v17))) (@Option.some.{0} (@Bool) (@_v9 _v17))))),
(∀ (_v18 : (∀ (_v18 : (@Nat)),
(∀ (_v19 : (@LE.le.{0} (@Nat) (@instLENat) _v18 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 (@_v11 _v18)) (@Option.none.{0} (@Bool)))))),
(∀ (_v19 : (∀ (_v19 : (@Nat)),
(∀ (_v20 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v11 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v19)),
(∀ (_v21 : (@LT.lt.{0} (@Nat) (@instLTNat) _v19 (@_v11 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 _v19) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v20 : (∀ (_v20 : (@Nat)),
(∀ (_v21 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v11 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v20)),
(∀ (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat) _v20 (@_v11 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))),
(@Exists.{(0 + 1)} (@Bool) (fun (_v23 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 _v20) (@Option.some.{0} (@Bool) _v23)))))))),
(∀ (_v21 : (∀ (_v21 : (@Nat)),
(∀ (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v11 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v21)),
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) _v21 (@_v11 (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 _v21) (@Option.some.{0} (@Bool) (@Bool.false))))))),
(∀ (_v22 : (∀ (_v22 : (@Nat)),
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v11 (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v22)),
(∀ (_v24 : (@LT.lt.{0} (@Nat) (@instLTNat) _v22 (@_v11 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 _v22) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat)
  (@instLENat) _v22 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v11
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v7)) (@Nat.decLe _v22 (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v11 (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))
  _v7))))))))),
(∀ (_v23 : (∀ (_v23 : (@Nat)),
(∀ (_v24 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v11 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v23)),
(∀ (_v25 : (@LT.lt.{0} (@Nat) (@instLTNat) _v23 (@_v11 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 _v23) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat)
  (@instLENat) _v23 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v11
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v8)) (@Nat.decLe _v23 (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v11 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))
  _v8))))))))),
(∀ (_v24 : (∀ (_v24 : (@Nat)),
(∀ (_v25 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v11 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) _v24)),
(∀ (_v26 : (@LT.lt.{0} (@Nat) (@instLTNat) _v24 (@_v11 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 _v24) (@Option.some.{0} (@Bool) (@Bool.false))))))),
(∀ (_v25 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v11 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))),
(let _v26 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine
  _v0)) _v1 _v2) := (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@CarryWindow.machine _v0)) _v1 _v2 (@CarryWindow.embed _v0 (@VirtualLeaf.embed _v0
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@IngressRepair.producer) (@Cursor.machine _v0) (@Cursor.q _v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (430 : Nat)
  (@instOfNatNat (430 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (93 : Nat) (@instOfNatNat (93 : Nat))) _v0)))))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@_v11 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))
  (@id.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@_v11 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (@Decidable.byContradiction (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v5 _v6) _v4) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v5 _v6) _v4) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (fun (_v26 : (@Not (@LT.lt.{0} (@Nat)
  (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v5 _v6) _v4) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)))) =>
(@CarryReadyCompletion.check_body._proof_3 _v1 _v2 _v4 _v5 _v6 _v25 _v26))))) (fun (_v26 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))) =>
(@_v10 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) _v26))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v27 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v27 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (8192 : Nat) (@instOfNatNat (8192 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v11 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat)))))) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@CarryWindow.machine _v0)) _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CarryWindow.machine _v0) _v1 _v2 _v27
  _v26) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine
  _v0)) _v1 _v2 (@CarryWindow.ready _v0) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@_v11
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@id.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@_v11
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))
  (@Decidable.byContradiction (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v5 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v5 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (fun (_v28 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v5 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)))) =>
(@CarryReadyCompletion.check_body._proof_4 _v1 _v2 _v4 _v5 _v6 _v25 _v28))))) (fun (_v28 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))) =>
(@CarryWindow.Target.image _v10 _v5 _v6 _v4 _v7 (@Pnp4.Frontier.ContractExpansion.bitLength _v8) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v8 (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) _v28))))) (@And (∀ (_v28 : (@Nat)),
(∀ (_v29 : (@LE.le.{0} (@Nat) (@instLENat) _v28 _v27)),
(@And (@LE.le.{0} (@Nat) (@instLENat) (@_v11 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)) _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CarryWindow.machine _v0) _v1 _v2 _v28 _v26)))) (@LE.le.{0} (@Nat)
  (@instLENat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)) _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CarryWindow.machine _v0) _v1 _v2 _v28 _v26))) (@_v11 (@OfNat.ofNat.{0}
  (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))))) (@And (∀ (_v28 : (@Nat)),
(∀ (_v29 : (@LE.le.{0} (@Nat) (@instLENat) _v28 _v27)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))
  _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CarryWindow.machine _v0) _v1 _v2 _v28 _v26))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@CarryWindow.machine _v0))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)) _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CarryWindow.machine _v0) _v1 _v2 _v28 _v26))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@CarryWindow.machine _v0)))))) (∀ (_v28 : (@Nat)),
(∀ (_v29 : (@LT.lt.{0} (@Nat) (@instLTNat) _v28 _v27)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))
  _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CarryWindow.machine _v0) _v1 _v2 _v28 _v26)) (@CarryWindow.ready
  _v0))))))))))))))))))))))))))))))))))))) := by
  exact @CarryReadyCompletion.check_body

-- Complete literal proposition for CarryReadyCompletion.check_body; original proof reused.
theorem PartACanonical.Surface.m0173 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Nat)),
(∀ (_v8 : (@Nat)),
(∀ (_v9 : (∀ (_v9 : (@Fin _v4)),
(@Bool))),
(∀ (_v10 : (∀ (_v10 : (@Nat)),
(@Option.{0} (@Bool)))),
(let _v11 : (∀ (_v11 : (@Nat)),
(@Nat)) := (fun (_v11 : (@Nat)) =>
(@CarryReadyCompletion.check_body.match_1.{(0 + 1)} (fun (_v12 : (@Nat)) =>
(@Nat)) _v11 (fun (_v12 : (@Unit)) =>
(@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v5 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (fun (_v12 : (@Unit)) =>
(@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v5 _v6) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))
  (fun (_v12 : (@Unit)) =>
(@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v5 _v6) _v4) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))) (fun (_v12 : (@Unit)) =>
(@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v5 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v6)) _v4) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))
  (fun (_v12 : (@Unit)) =>
(@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v5 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v6)) _v4) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))
  (fun (_v12 : (@Unit)) =>
(@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v5 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v6)) _v4) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))
  (fun (_v12 : (@Nat)) =>
(@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v5 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v6)) _v4) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 :
  Nat)))))));
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v5)),
(∀ (_v13 : (@LE.le.{0} (@Nat) (@instLENat) _v7 _v6)),
(∀ (_v14 : (@LE.le.{0} (@Nat) (@instLENat) _v8 _v6)),
(∀ (_v15 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 _v3) (@Option.none.{0} (@Bool)))),
(∀ (_v16 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Option.none.{0} (@Bool)))),
(∀ (_v17 : (∀ (_v17 : (@Fin _v4)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v3 _v4) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat)
  (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Fin.val _v4 _v17))) (@Option.some.{0} (@Bool) (@_v9 _v17))))),
(∀ (_v18 : (∀ (_v18 : (@Nat)),
(∀ (_v19 : (@LE.le.{0} (@Nat) (@instLENat) _v18 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 (@_v11 _v18)) (@Option.none.{0} (@Bool)))))),
(∀ (_v19 : (∀ (_v19 : (@Nat)),
(∀ (_v20 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v11 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v19)),
(∀ (_v21 : (@LT.lt.{0} (@Nat) (@instLTNat) _v19 (@_v11 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 _v19) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v20 : (∀ (_v20 : (@Nat)),
(∀ (_v21 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v11 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v20)),
(∀ (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat) _v20 (@_v11 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))),
(@Exists.{(0 + 1)} (@Bool) (fun (_v23 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 _v20) (@Option.some.{0} (@Bool) _v23)))))))),
(∀ (_v21 : (∀ (_v21 : (@Nat)),
(∀ (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v11 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v21)),
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) _v21 (@_v11 (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 _v21) (@Option.some.{0} (@Bool) (@Bool.false))))))),
(∀ (_v22 : (∀ (_v22 : (@Nat)),
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v11 (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v22)),
(∀ (_v24 : (@LT.lt.{0} (@Nat) (@instLTNat) _v22 (@_v11 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 _v22) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat)
  (@instLENat) _v22 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v11
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v7)) (@Nat.decLe _v22 (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v11 (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))
  _v7))))))))),
(∀ (_v23 : (∀ (_v23 : (@Nat)),
(∀ (_v24 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v11 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v23)),
(∀ (_v25 : (@LT.lt.{0} (@Nat) (@instLTNat) _v23 (@_v11 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 _v23) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat)
  (@instLENat) _v23 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v11
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v8)) (@Nat.decLe _v23 (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v11 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))
  _v8))))))))),
(∀ (_v24 : (∀ (_v24 : (@Nat)),
(∀ (_v25 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v11 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) _v24)),
(∀ (_v26 : (@LT.lt.{0} (@Nat) (@instLTNat) _v24 (@_v11 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v10 _v24) (@Option.some.{0} (@Bool) (@Bool.false))))))),
(∀ (_v25 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v11 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))),
(let _v26 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine
  _v0)) _v1 _v2) := (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@CarryWindow.machine _v0)) _v1 _v2 (@CarryWindow.embed _v0 (@VirtualLeaf.embed _v0
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@IngressRepair.producer) (@Cursor.machine _v0) (@Cursor.q _v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (430 : Nat)
  (@instOfNatNat (430 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (93 : Nat) (@instOfNatNat (93 : Nat))) _v0)))))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@_v11 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))
  (@id.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@_v11 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (@Decidable.byContradiction (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v5 _v6) _v4) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v5 _v6) _v4) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (fun (_v26 : (@Not (@LT.lt.{0} (@Nat)
  (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v5 _v6) _v4) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)))) =>
(@CarryReadyCompletion.check_body._proof_3 _v1 _v2 _v4 _v5 _v6 _v25 _v26))))) (fun (_v26 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))) =>
(@_v10 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) _v26))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v27 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v27 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (8192 : Nat) (@instOfNatNat (8192 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v11 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat)))))) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@CarryWindow.machine _v0)) _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CarryWindow.machine _v0) _v1 _v2 _v27
  _v26) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine
  _v0)) _v1 _v2 (@CarryWindow.ready _v0) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@_v11
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@id.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@_v11
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))
  (@Decidable.byContradiction (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v5 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v5 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (fun (_v28 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v5 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)))) =>
(@CarryReadyCompletion.check_body._proof_4 _v1 _v2 _v4 _v5 _v6 _v25 _v28))))) (fun (_v28 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))) =>
(@CarryWindow.Target.image _v10 _v5 _v6 _v4 _v7 (@Pnp4.Frontier.ContractExpansion.bitLength _v8) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v8 (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) _v28))))) (@And (∀ (_v28 : (@Nat)),
(∀ (_v29 : (@LE.le.{0} (@Nat) (@instLENat) _v28 _v27)),
(@And (@LE.le.{0} (@Nat) (@instLENat) (@_v11 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)) _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CarryWindow.machine _v0) _v1 _v2 _v28 _v26)))) (@LE.le.{0} (@Nat)
  (@instLENat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)) _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CarryWindow.machine _v0) _v1 _v2 _v28 _v26))) (@_v11 (@OfNat.ofNat.{0}
  (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))))) (@And (∀ (_v28 : (@Nat)),
(∀ (_v29 : (@LE.le.{0} (@Nat) (@instLENat) _v28 _v27)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))
  _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CarryWindow.machine _v0) _v1 _v2 _v28 _v26))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@CarryWindow.machine _v0))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)) _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CarryWindow.machine _v0) _v1 _v2 _v28 _v26))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@CarryWindow.machine _v0)))))) (∀ (_v28 : (@Nat)),
(∀ (_v29 : (@LT.lt.{0} (@Nat) (@instLTNat) _v28 _v27)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))
  _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CarryWindow.machine _v0) _v1 _v2 _v28 _v26)) (@CarryWindow.ready
  _v0))))))))))))))))))))))))))))))))))))) := by
  exact @CarryReadyCompletion.check_body

-- Independent literal expected type for CarryReadyCompletion.check_projection_ready.
noncomputable def PartACanonical.Types.p0273 :
(let _v0 : (@Pnp3.Complexity.Uniform.V1.Bitstring (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat)))) :=
  (fun (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))))) =>
(@Bool.or (@Bool.or (@Bool.or (@Bool.or (@Bool.or (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat)
  (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))) _v0) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat)
  (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))) _v0) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat)
  (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))) _v0) (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat)
  (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))) _v0) (@OfNat.ofNat.{0}
  (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat)
  (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))) _v0) (@OfNat.ofNat.{0}
  (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat)
  (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))) _v0) (@OfNat.ofNat.{0}
  (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))));
(let _v1 : (@Pnp3.Complexity.Uniform.V1.Bitstring (@OfNat.ofNat.{0} (@Nat) (14 : Nat) (@instOfNatNat (14 : Nat)))) :=
  (fun (_v1 : (@Fin (@OfNat.ofNat.{0} (@Nat) (14 : Nat) (@instOfNatNat (14 : Nat))))) =>
(@Bool.false));
(@Exists.{(0 + 1)} (@Nat) (fun (_v2 : (@Nat)) =>
(@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine (@OfNat.ofNat.{0} (@Nat) (0
  : Nat) (@instOfNatNat (0 : Nat)))))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (13 : Nat)
  (@instOfNatNat (13 : Nat))) (@OfNat.ofNat.{0} (@Nat) (14 : Nat) (@instOfNatNat (14 : Nat)))) (@OfNat.ofNat.{0} (@Nat)
  (28224 : Nat) (@instOfNatNat (28224 : Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CarryWindow.machine
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))) (@OfNat.ofNat.{0} (@Nat) (14 : Nat) (@instOfNatNat (14 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (28224 : Nat) (@instOfNatNat (28224 : Nat))) _v2
  (@Pnp3.Complexity.Uniform.V1.initialConfig (@CarryWindow.machine (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (14 : Nat) (@instOfNatNat (14 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (28224 : Nat)
  (@instOfNatNat (28224 : Nat))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair (@OfNat.ofNat.{0} (@Nat) (13 : Nat)
  (@instOfNatNat (13 : Nat))) (@OfNat.ofNat.{0} (@Nat) (14 : Nat) (@instOfNatNat (14 : Nat))) _v0 _v1))))
  (@CarryWindow.ready (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))))))) := by
  exact @CarryReadyCompletion.check_projection_ready

-- Complete literal proposition for CarryReadyCompletion.check_projection_ready; original proof reused.
theorem PartACanonical.Surface.m0174 :
(let _v0 : (@Pnp3.Complexity.Uniform.V1.Bitstring (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat)))) :=
  (fun (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))))) =>
(@Bool.or (@Bool.or (@Bool.or (@Bool.or (@Bool.or (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat)
  (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))) _v0) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat)
  (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))) _v0) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat)
  (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))) _v0) (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat)
  (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))) _v0) (@OfNat.ofNat.{0}
  (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat)
  (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))) _v0) (@OfNat.ofNat.{0}
  (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat)
  (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))) _v0) (@OfNat.ofNat.{0}
  (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))));
(let _v1 : (@Pnp3.Complexity.Uniform.V1.Bitstring (@OfNat.ofNat.{0} (@Nat) (14 : Nat) (@instOfNatNat (14 : Nat)))) :=
  (fun (_v1 : (@Fin (@OfNat.ofNat.{0} (@Nat) (14 : Nat) (@instOfNatNat (14 : Nat))))) =>
(@Bool.false));
(@Exists.{(0 + 1)} (@Nat) (fun (_v2 : (@Nat)) =>
(@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine (@OfNat.ofNat.{0} (@Nat) (0
  : Nat) (@instOfNatNat (0 : Nat)))))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (13 : Nat)
  (@instOfNatNat (13 : Nat))) (@OfNat.ofNat.{0} (@Nat) (14 : Nat) (@instOfNatNat (14 : Nat)))) (@OfNat.ofNat.{0} (@Nat)
  (28224 : Nat) (@instOfNatNat (28224 : Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CarryWindow.machine
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))) (@OfNat.ofNat.{0} (@Nat) (14 : Nat) (@instOfNatNat (14 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (28224 : Nat) (@instOfNatNat (28224 : Nat))) _v2
  (@Pnp3.Complexity.Uniform.V1.initialConfig (@CarryWindow.machine (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (14 : Nat) (@instOfNatNat (14 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (28224 : Nat)
  (@instOfNatNat (28224 : Nat))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair (@OfNat.ofNat.{0} (@Nat) (13 : Nat)
  (@instOfNatNat (13 : Nat))) (@OfNat.ofNat.{0} (@Nat) (14 : Nat) (@instOfNatNat (14 : Nat))) _v0 _v1))))
  (@CarryWindow.ready (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))))))) := by
  exact @CarryReadyCompletion.check_projection_ready

-- Independent literal expected type for CarryReadyCompletion.projection_ready.
noncomputable def PartACanonical.Types.p0275 :
(let _v0 : (@Pnp3.Complexity.Uniform.V1.Bitstring (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat)))) :=
  (fun (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))))) =>
(@Bool.or (@Bool.or (@Bool.or (@Bool.or (@Bool.or (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat)
  (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))) _v0) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat)
  (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))) _v0) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat)
  (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))) _v0) (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat)
  (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))) _v0) (@OfNat.ofNat.{0}
  (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat)
  (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))) _v0) (@OfNat.ofNat.{0}
  (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat)
  (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))) _v0) (@OfNat.ofNat.{0}
  (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))));
(let _v1 : (@Pnp3.Complexity.Uniform.V1.Bitstring (@OfNat.ofNat.{0} (@Nat) (14 : Nat) (@instOfNatNat (14 : Nat)))) :=
  (fun (_v1 : (@Fin (@OfNat.ofNat.{0} (@Nat) (14 : Nat) (@instOfNatNat (14 : Nat))))) =>
(@Bool.false));
(@Exists.{(0 + 1)} (@Nat) (fun (_v2 : (@Nat)) =>
(@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine (@OfNat.ofNat.{0} (@Nat) (0
  : Nat) (@instOfNatNat (0 : Nat)))))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (13 : Nat)
  (@instOfNatNat (13 : Nat))) (@OfNat.ofNat.{0} (@Nat) (14 : Nat) (@instOfNatNat (14 : Nat)))) (@OfNat.ofNat.{0} (@Nat)
  (28224 : Nat) (@instOfNatNat (28224 : Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CarryWindow.machine
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))) (@OfNat.ofNat.{0} (@Nat) (14 : Nat) (@instOfNatNat (14 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (28224 : Nat) (@instOfNatNat (28224 : Nat))) _v2
  (@Pnp3.Complexity.Uniform.V1.initialConfig (@CarryWindow.machine (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (14 : Nat) (@instOfNatNat (14 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (28224 : Nat)
  (@instOfNatNat (28224 : Nat))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair (@OfNat.ofNat.{0} (@Nat) (13 : Nat)
  (@instOfNatNat (13 : Nat))) (@OfNat.ofNat.{0} (@Nat) (14 : Nat) (@instOfNatNat (14 : Nat))) _v0 _v1))))
  (@CarryWindow.ready (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))))))) := by
  exact @CarryReadyCompletion.projection_ready

-- Complete literal proposition for CarryReadyCompletion.projection_ready; original proof reused.
theorem PartACanonical.Surface.m0176 :
(let _v0 : (@Pnp3.Complexity.Uniform.V1.Bitstring (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat)))) :=
  (fun (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))))) =>
(@Bool.or (@Bool.or (@Bool.or (@Bool.or (@Bool.or (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat)
  (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))) _v0) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat)
  (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))) _v0) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat)
  (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))) _v0) (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat)
  (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))) _v0) (@OfNat.ofNat.{0}
  (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat)
  (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))) _v0) (@OfNat.ofNat.{0}
  (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat)
  (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))) _v0) (@OfNat.ofNat.{0}
  (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))));
(let _v1 : (@Pnp3.Complexity.Uniform.V1.Bitstring (@OfNat.ofNat.{0} (@Nat) (14 : Nat) (@instOfNatNat (14 : Nat)))) :=
  (fun (_v1 : (@Fin (@OfNat.ofNat.{0} (@Nat) (14 : Nat) (@instOfNatNat (14 : Nat))))) =>
(@Bool.false));
(@Exists.{(0 + 1)} (@Nat) (fun (_v2 : (@Nat)) =>
(@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine (@OfNat.ofNat.{0} (@Nat) (0
  : Nat) (@instOfNatNat (0 : Nat)))))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (13 : Nat)
  (@instOfNatNat (13 : Nat))) (@OfNat.ofNat.{0} (@Nat) (14 : Nat) (@instOfNatNat (14 : Nat)))) (@OfNat.ofNat.{0} (@Nat)
  (28224 : Nat) (@instOfNatNat (28224 : Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CarryWindow.machine
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))) (@OfNat.ofNat.{0} (@Nat) (14 : Nat) (@instOfNatNat (14 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (28224 : Nat) (@instOfNatNat (28224 : Nat))) _v2
  (@Pnp3.Complexity.Uniform.V1.initialConfig (@CarryWindow.machine (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (14 : Nat) (@instOfNatNat (14 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (28224 : Nat)
  (@instOfNatNat (28224 : Nat))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair (@OfNat.ofNat.{0} (@Nat) (13 : Nat)
  (@instOfNatNat (13 : Nat))) (@OfNat.ofNat.{0} (@Nat) (14 : Nat) (@instOfNatNat (14 : Nat))) _v0 _v1))))
  (@CarryWindow.ready (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))))))) := by
  exact @CarryReadyCompletion.projection_ready

-- Independent literal expected type for CarryReadyCompletion.raw.
noncomputable def PartACanonical.Types.p0276 :
(∀ (_v0 : (@Nat)),
(@CarryWindow.Target.Raw _v0)) := by
  exact @CarryReadyCompletion.raw

-- Complete literal proposition for CarryReadyCompletion.raw; original proof reused.
theorem PartACanonical.Surface.m0177 :
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
(let _v22 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11) := (@Pnp3.Complexity.Uniform.V1.initialConfig
  (@CarryWindow.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4));
(let _v23 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@IngressRepair.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig (@IngressRepair.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair
  _v1 _v2 _v3 _v4));
(let _v24 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11)) := (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v9 _v7) _v12) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) _v8);
(let _v25 : (∀ (_v25 : (∀ (_v25 : (@Nat)),
(@Option.{0} (@Bool)))),
(Sort 0)) := (fun (_v25 : (∀ (_v25 : (@Nat)),
(@Option.{0} (@Bool)))) =>
(@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v12) (fun
  (_v26 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v12)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v9 (@Cursor.Target.M _v0 _v12 _v7)) (@And (∀ (_v27 : (@Fin (@Cursor.Target.W _v0
  _v12))),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v3 _v4) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Cursor.Target.M _v0 _v12 _v7) (@Fin.val (@Cursor.Target.W
  _v0 _v12) _v27))) (@Bool.false))) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Pnp3.Models.Circuit _v12))
  (@Pnp4.Frontier.TreeCircuitWitnessCodec.decode (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v12
  (fun (_v27 : (@Fin (@Pnp4.Frontier.TreeCircuitWitnessCodec.witnessBits (@Pnp4.Frontier.ContractExpansion.thresholdPoly
  _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))
  _v12))) =>
(@Bool.false))) (@Option.some.{0} (@Pnp3.Models.Circuit _v12) (@Pnp3.Models.Circuit.input _v12 (@Fin.mk _v12
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v26)))) (@Exists.{(0 + 1)} (@Nat) (fun (_v27 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v28 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v28 _v27) (@And (@LE.le.{0} (@Nat) (@instLENat) _v27 (@HMul.hMul.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2147483648 : Nat) (@instOfNatNat (2147483648 : Nat))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat))))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 :
  Nat)))))) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@IngressRepair.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@IngressRepair.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v27 _v23) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@IngressRepair.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@VirtualLeaf.entry _v0) _v24 (fun (_v29 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11))) =>
(@_v25 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  _v11) _v29))))) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@IngressRepair.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@IngressRepair.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v28 _v23)
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@IngressRepair.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@VirtualLeaf.entry _v0) _v24 (fun (_v29 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11))) =>
(@_v25 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  _v11) _v29))))) (@And (∀ (_v29 : (@Nat)),
(∀ (_v30 : (@LT.lt.{0} (@Nat) (@instLTNat) _v29 _v28)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@IngressRepair.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@IngressRepair.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@IngressRepair.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v29 _v23))
  (@VirtualLeaf.entry _v0)))) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@CarryWindow.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v28 _v22)
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@CarryWindow.embed _v0 (@CanonicalLeaf.entry _v0))
  _v24 (fun (_v29 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2) _v11))) =>
(@_v25 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  _v11) _v29))))) (@And (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v28 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4294967296 : Nat) (@instOfNatNat (4294967296 : Nat))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat))))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 :
  Nat)))))) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@CarryWindow.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CarryWindow.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v28 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) _v22)
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@CarryWindow.embed _v0 (@CanonicalLeaf.result _v0
  (@Bool.false))) _v24 (@Function.update.{(0 + 1), (0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11)) (fun (_v29 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11))) =>
(@Option.{0} (@Bool))) (@instDecidableEqFin (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11)) (fun (_v29 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11))) =>
(@_v25 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  _v11) _v29))) _v24 (@Option.some.{0} (@Bool) (@Bool.false))))) (@And (∀ (_v29 : (@Nat)),
(∀ (_v30 : (@LE.le.{0} (@Nat) (@instLENat) _v29 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v28 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@CarryWindow.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v29 _v22))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@CarryWindow.machine _v0))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@CarryWindow.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v29 _v22))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@CarryWindow.machine _v0)))))) (∀ (_v29 : (@Nat)),
(∀ (_v30 : (@LT.lt.{0} (@Nat) (@instLTNat) _v29 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v28 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))),
(∀ (_v31 : (@Bool)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@CarryWindow.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v29 _v22))
  (@CarryWindow.embed _v0 (@CanonicalLeaf.result _v0 _v31)))))))))))))))))))))))));
(@And (∀ (_v26 : (@Eq.{(0 + 1)} (@Nat) _v15 _v9)),
(@_v25 _v18)) (∀ (_v26 : (@LT.lt.{0} (@Nat) (@instLTNat) _v15 _v9)),
(@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v16)) _v12) (@OfNat.ofNat.{0}
  (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11)) (fun (_v27 :
  (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v16)) _v12) (@OfNat.ofNat.{0} (@Nat) (7 :
  Nat) (@instOfNatNat (7 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11))) =>
(@Or (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v16 (@Pnp4.Frontier.ContractExpansion.bitLength _v12)) (@And (@LT.lt.{0}
  (@Nat) (@instLTNat) _v9 (@Cursor.Target.M _v0 _v12 _v7)) (@_v25 (@Cursor.Target.image _v18 _v0 _v9 _v12 _v7 _v14))))
  (@And (@LE.le.{0} (@Nat) (@instLENat) (@Pnp4.Frontier.ContractExpansion.bitLength _v12) _v16) (@Or (@And (@LE.le.{0}
  (@Nat) (@instLENat) (@Cursor.Target.W _v0 _v12) _v16) (@Exists.{(0 + 1)} (@Nat) (fun (_v28 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v29 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v28 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (268435456 : Nat) (@instOfNatNat (268435456 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@And (@LE.le.{0} (@Nat) (@instLENat) _v29
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (1048576 : Nat)
  (@instOfNatNat (1048576 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))))) (@And (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v28 _v29) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (8589934592 : Nat) (@instOfNatNat (8589934592 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))) (@And (@Eq.{(0 + 1)}
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@CarryWindow.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v28 _v22)
  (@CarryWindow.config _v0 _v10 _v11 (@VirtualLeaf.config _v0 _v10 _v11
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@IngressRepair.producer) (@Cursor.machine _v0) _v10 _v11
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0)) _v10
  _v11 (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0}
  (@Nat) (430 : Nat) (@instOfNatNat (430 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (93 : Nat) (@instOfNatNat (93 : Nat))) _v0))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 _v16) _v12) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (@CarryWindow.Target.Raw._proof_3 _v0 _v1 _v2 _v6 _v7 _v27)) (fun (_v30 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11))) =>
(@CappedWeight.Target.image _v21 _v13 _v12 _v14 _v16 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v12 _v0) _v0) (@Cursor.Target.W
  _v0 _v12) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11) _v30)))))))) (@And (∀ (_v30 :
  (@Nat)),
(∀ (_v31 : (@LT.lt.{0} (@Nat) (@instLTNat) _v30 _v28)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@CarryWindow.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v30 _v22))
  (@CarryWindow.embed _v0 (@VirtualLeaf.embed _v0 (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight
  (@IngressRepair.producer) (@Cursor.machine _v0) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (430 : Nat) (@instOfNatNat (430 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (93 : Nat) (@instOfNatNat (93 : Nat)))
  _v0))))))))) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@CarryWindow.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CarryWindow.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v28 _v29) _v22) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@CarryWindow.ready _v0) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))) (@CarryWindow.Target.Raw._proof_4 _v0 _v1 _v2 _v6 _v7 _v27)) (fun (_v30 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11))) =>
(@CarryWindow.Target.image (@CappedWeight.Target.image _v21 _v13 _v12 _v14 _v16 (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) _v12 _v0) _v0) (@Cursor.Target.W _v0 _v12) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v14 _v16 _v12 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v12 _v0) _v0) (@Pnp4.Frontier.ContractExpansion.bitLength
  (@Cursor.Target.W _v0 _v12)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 :
  Nat) (@instOfNatNat (0 : Nat))) (@Cursor.Target.W _v0 _v12) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11) _v30))))) (@And (∀ (_v30 : (@Nat)),
(∀ (_v31 : (@LE.le.{0} (@Nat) (@instLENat) _v30 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v28 _v29))),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@CarryWindow.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v30 _v22))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@CarryWindow.machine _v0))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@CarryWindow.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v30 _v22))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@CarryWindow.machine _v0)))))) (∀ (_v30 : (@Nat)),
(∀ (_v31 : (@LT.lt.{0} (@Nat) (@instLTNat) _v30 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v28 _v29))),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@CarryWindow.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v30 _v22))
  (@CarryWindow.ready _v0)))))))))))))))) (@Exists.{(0 + 1)} (@Nat) (fun (_v28 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v29 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v30 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v31 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v32 : (@Nat)) =>
(@And (@Or (@Exists.{(0 + 1)} (@Nat) (fun (_v33 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v34 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v35 : (@Nat)) =>
(@And (@LT.lt.{0} (@Nat) (@instLTNat) _v33 _v0) (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v34 (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v12 _v33)) (@And
  (@LT.lt.{0} (@Nat) (@instLTNat) _v35 _v12) (@And (@Eq.{(0 + 1)} (@Nat) _v16 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  _v34 _v12) _v35)) (@And (@Eq.{(0 + 1)} (@Nat) _v28 (@Pnp4.Frontier.ContractExpansion.bitLength _v12)) (@And (@Eq.{(0 +
  1)} (@Nat) _v29 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HSub.hSub.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0}
  (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v12 _v33) _v34) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@And (@Eq.{(0 + 1)} (@Nat) _v30 _v16) (@And (@Eq.{(0 + 1)} (@Nat) _v31 (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Eq.{(0 + 1)} (@Nat) _v32 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v35 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))))))))))))))))
  (@Or (@Exists.{(0 + 1)} (@Nat) (fun (_v33 : (@Nat)) =>
(@And (@LT.lt.{0} (@Nat) (@instLTNat) _v33 _v0) (@And (@Eq.{(0 + 1)} (@Nat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v12 _v0) _v33) _v16) (@And (@Eq.{(0 + 1)} (@Nat) _v28
  (@Pnp4.Frontier.ContractExpansion.bitLength _v12)) (@And (@Eq.{(0 + 1)} (@Nat) _v29 _v16) (@And (@Eq.{(0 + 1)} (@Nat)
  _v30 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@And (@Eq.{(0 + 1)} (@Nat) _v31 (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Eq.{(0 + 1)} (@Nat) _v32 (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))))))))))) (@Or (@Exists.{(0 + 1)} (@Nat) (fun (_v33 : (@Nat)) =>
(@And (@LT.lt.{0} (@Nat) (@instLTNat) _v33 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@And (@Eq.{(0
  + 1)} (@Nat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp4.Frontier.ContractExpansion.bitLength _v12) _v33) _v16) (@And (@Eq.{(0 + 1)} (@Nat) _v28 _v16) (@And (@Eq.{(0 +
  1)} (@Nat) _v29 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v12 _v0) _v0))
  (@And (@Eq.{(0 + 1)} (@Nat) _v30 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@And (@Eq.{(0 + 1)}
  (@Nat) _v31 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Eq.{(0 + 1)} (@Nat) _v32 (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))))))))))) (@Exists.{(0 + 1)} (@Nat) (fun (_v33 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v34 : (@Nat)) =>
(@And (@LT.lt.{0} (@Nat) (@instLTNat) _v33 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@Pnp4.Frontier.ContractExpansion.bitLength _v12) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v34 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) _v12 _v0) _v0)) (@And (@Eq.{(0 + 1)} (@Nat) _v16 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  _v33 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v12 _v0) _v0)) _v34)) (@And
  (@Eq.{(0 + 1)} (@Nat) _v28 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat))
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp4.Frontier.ContractExpansion.bitLength _v12) (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))) _v33) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@And
  (@Eq.{(0 + 1)} (@Nat) _v29 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat))
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v12 _v0) _v0) _v34) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat))))) (@And (@Eq.{(0 + 1)} (@Nat) _v30 _v16) (@And (@Eq.{(0 + 1)} (@Nat) _v31 _v34) (@Eq.{(0 + 1)} (@Nat) _v32
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))))))))))))))))) (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v9
  (@Cursor.Target.M _v0 _v12 _v7)) (@_v25 (@Cursor.Target.image _v18 _v0 _v9 _v12 _v7
  _v14)))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @CarryReadyCompletion.raw

-- Independent literal expected type for CarryWindow.Target.Body.
noncomputable def PartACanonical.Types.p0277 :
(∀ (_v0 : (@Nat)),
(Sort 0)) := by
  exact @CarryWindow.Target.Body

-- Independent literal expected type for CarryWindow.Target.Raw.
noncomputable def PartACanonical.Types.p0278 :
(∀ (_v0 : (@Nat)),
(Sort 0)) := by
  exact @CarryWindow.Target.Raw

-- Independent literal expected type for CarryWindow.Target.image.
noncomputable def PartACanonical.Types.p0279 :
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
(@Option.{0} (@Bool)))))))))))) := by
  exact @CarryWindow.Target.image

-- Independent literal expected type for CarryWindow.config.
noncomputable def PartACanonical.Types.p0280 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine
  _v0)) _v1 _v2)),
(@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)) _v1
  _v2))))) := by
  exact @CarryWindow.config

-- Independent literal expected type for CarryWindow.controls.
noncomputable def PartACanonical.Types.p0281 :
(∀ (_v0 : (@Nat)),
(@And (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0)) (@OfNat.ofNat.{0} (@Nat) (25 : Nat)
  (@instOfNatNat (25 : Nat))))) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@CarryWindow.machine _v0))) (@Pnp3.Complexity.Uniform.V1.UniformTM.start (@CarryWindow.machine _v0))
  (@CarryWindow.embed _v0 (@Pnp3.Complexity.Uniform.V1.UniformTM.start (@CanonicalLeaf.machine _v0)))) (@And (@Eq.{(0 +
  1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@CarryWindow.machine _v0)) (@CarryWindow.embed _v0
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@CanonicalLeaf.machine _v0)))) (@And (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@CarryWindow.machine _v0)) (@CarryWindow.embed _v0
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@CanonicalLeaf.machine _v0)))) (@Function.Injective.{(0 + 1), (0 + 1)}
  (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0))) (@Fin (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@CanonicalLeaf.machine _v0)) (@OfNat.ofNat.{0} (@Nat) (25 : Nat) (@instOfNatNat (25 : Nat))))) (@CarryWindow.embed
  _v0))))))) := by
  exact @CarryWindow.controls

-- Complete literal proposition for CarryWindow.controls; original proof reused.
theorem PartACanonical.Surface.m0178 :
(∀ (_v0 : (@Nat)),
(@And (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0)) (@OfNat.ofNat.{0} (@Nat) (25 : Nat)
  (@instOfNatNat (25 : Nat))))) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@CarryWindow.machine _v0))) (@Pnp3.Complexity.Uniform.V1.UniformTM.start (@CarryWindow.machine _v0))
  (@CarryWindow.embed _v0 (@Pnp3.Complexity.Uniform.V1.UniformTM.start (@CanonicalLeaf.machine _v0)))) (@And (@Eq.{(0 +
  1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@CarryWindow.machine _v0)) (@CarryWindow.embed _v0
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@CanonicalLeaf.machine _v0)))) (@And (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@CarryWindow.machine _v0)) (@CarryWindow.embed _v0
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@CanonicalLeaf.machine _v0)))) (@Function.Injective.{(0 + 1), (0 + 1)}
  (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0))) (@Fin (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@CanonicalLeaf.machine _v0)) (@OfNat.ofNat.{0} (@Nat) (25 : Nat) (@instOfNatNat (25 : Nat))))) (@CarryWindow.embed
  _v0))))))) := by
  exact @CarryWindow.controls

-- Independent literal expected type for CarryWindow.embed.
noncomputable def PartACanonical.Types.p0282 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0)))),
(@Fin (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0)) (@OfNat.ofNat.{0} (@Nat) (25 : Nat)
  (@instOfNatNat (25 : Nat))))))) := by
  exact @CarryWindow.embed

-- Independent literal expected type for CarryWindow.extra.
noncomputable def PartACanonical.Types.p0283 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@OfNat.ofNat.{0} (@Nat) (25 : Nat) (@instOfNatNat (25 : Nat))))),
(@Fin (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0)) (@OfNat.ofNat.{0} (@Nat) (25 : Nat)
  (@instOfNatNat (25 : Nat))))))) := by
  exact @CarryWindow.extra

-- Independent literal expected type for CarryWindow.machine.
noncomputable def PartACanonical.Types.p0284 :
(∀ (_v0 : (@Nat)),
(@Pnp3.Complexity.Uniform.V1.UniformTM)) := by
  exact @CarryWindow.machine

-- Independent literal expected type for CarryWindow.missing_payload.
noncomputable def PartACanonical.Types.p0285 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v2)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.tagMatches (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v3 _v4))
  (@Bool.true))),
(∀ (_v7 : (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros?
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2
  (@Bool) _v3 _v4)) (@Option.some.{0} (@Nat) _v5))),
(∀ (_v8 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v5)),
(∀ (_v9 : (@Eq.{(0 + 1)} (@Nat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat))) _v5))),
(@Exists.{(0 + 1)} (@Nat) (fun (_v10 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v10 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (128 : Nat) (@instOfNatNat (128 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat)))))) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CarryWindow.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v10 (@Pnp3.Complexity.Uniform.V1.initialConfig (@CarryWindow.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@CarryWindow.machine _v0))) (@Eq.{(0 + 1)} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v1 _v2 _v3 _v4)
  (@Bool.false)))))))))))))))) := by
  exact @CarryWindow.missing_payload

-- Complete literal proposition for CarryWindow.missing_payload; original proof reused.
theorem PartACanonical.Surface.m0179 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v2)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.tagMatches (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v3 _v4))
  (@Bool.true))),
(∀ (_v7 : (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros?
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2
  (@Bool) _v3 _v4)) (@Option.some.{0} (@Nat) _v5))),
(∀ (_v8 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v5)),
(∀ (_v9 : (@Eq.{(0 + 1)} (@Nat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat))) _v5))),
(@Exists.{(0 + 1)} (@Nat) (fun (_v10 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v10 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (128 : Nat) (@instOfNatNat (128 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat)))))) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CarryWindow.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v10 (@Pnp3.Complexity.Uniform.V1.initialConfig (@CarryWindow.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@CarryWindow.machine _v0))) (@Eq.{(0 + 1)} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v1 _v2 _v3 _v4)
  (@Bool.false)))))))))))))))) := by
  exact @CarryWindow.missing_payload

-- Independent literal expected type for CarryWindow.prepared_carry.
noncomputable def PartACanonical.Types.p0286 :
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
(∀ (_v9 : (@LE.le.{0} (@Nat) (@instLENat) _v6 _v4)),
(∀ (_v10 : (∀ (_v10 : (@Nat)),
(∀ (_v11 : (@LE.le.{0} (@Nat) (@instLENat) _v10 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v8 (@CarryWindow.prepared_carry.match_1.{(0 + 1)} (fun (_v12 : (@Nat)) =>
(@Nat)) _v10 (fun (_v12 : (@Unit)) =>
(@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (fun (_v12 : (@Unit)) =>
(@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))
  (fun (_v12 : (@Unit)) =>
(@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 _v4) _v5) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))) (fun (_v12 : (@Unit)) =>
(@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)) _v5) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))
  (fun (_v12 : (@Unit)) =>
(@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v4)) _v5) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))
  (fun (_v12 : (@Unit)) =>
(@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v4)) _v5) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))
  (fun (_v12 : (@Nat)) =>
(@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v4)) _v5) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))))))
  (@Option.none.{0} (@Bool)))))),
(∀ (_v11 : (∀ (_v11 : (@Nat)),
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v11)),
(∀ (_v13 : (@LT.lt.{0} (@Nat) (@instLTNat) _v11 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) _v5) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))))),
(@Exists.{(0 + 1)} (@Bool) (fun (_v14 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v8 _v11) (@Option.some.{0} (@Bool) _v14)))))))),
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v4)) _v5) (@OfNat.ofNat.{0} (@Nat)
  (7 : Nat) (@instOfNatNat (7 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))),
(let _v13 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) _v6
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v6) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v4)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v5))
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v4)) (@HMul.hMul.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))) _v5)) (@OfNat.ofNat.{0} (@Nat) (10 : Nat) (@instOfNatNat (10 : Nat))));
(let _v14 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine
  _v0)) _v1 _v2) := (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@CarryWindow.machine _v0)) _v1 _v2 (@CarryWindow.embed _v0 (@VirtualLeaf.embed _v0
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@IngressRepair.producer) (@Cursor.machine _v0) (@Cursor.q _v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (430 : Nat)
  (@instOfNatNat (430 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (93 : Nat) (@instOfNatNat (93 : Nat))) _v0)))))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) _v5) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (@Decidable.byContradiction (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) _v5)
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))
  (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 _v4) _v5) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (fun (_v14 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) _v5)
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)))) =>
(@CarryWindow.prepared_carry._proof_3 _v1 _v2 _v3 _v4 _v5 _v6 _v9 _v12 _v14)))) (fun (_v14 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))) =>
(@CarryWindow.Target.image _v8 _v3 _v4 _v5 _v4 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v6 _v7
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)
  _v14))));
(@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@CarryWindow.machine _v0)) _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CarryWindow.machine _v0) _v1 _v2 _v13
  _v14) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine
  _v0)) _v1 _v2 (@CarryWindow.extra _v0 (@Fin.mk (@OfNat.ofNat.{0} (@Nat) (25 : Nat) (@instOfNatNat (25 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (23 : Nat) (@instOfNatNat (23 : Nat))) (@of_decide_eq_true (@LT.lt.{0} (@Nat) (@instLTNat)
  (@OfNat.ofNat.{0} (@Nat) (23 : Nat) (@instOfNatNat (23 : Nat))) (@OfNat.ofNat.{0} (@Nat) (25 : Nat) (@instOfNatNat (25 :
  Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (23 : Nat) (@instOfNatNat (23 : Nat))) (@OfNat.ofNat.{0} (@Nat) (25 : Nat)
  (@instOfNatNat (25 : Nat)))) (@id.{0} (@Eq.{(0 + 1)} (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat) (@instLTNat)
  (@OfNat.ofNat.{0} (@Nat) (23 : Nat) (@instOfNatNat (23 : Nat))) (@OfNat.ofNat.{0} (@Nat) (25 : Nat) (@instOfNatNat (25 :
  Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (23 : Nat) (@instOfNatNat (23 : Nat))) (@OfNat.ofNat.{0} (@Nat) (25 : Nat)
  (@instOfNatNat (25 : Nat))))) (@Bool.true)) (@Eq.refl.{(0 + 1)} (@Bool) (@Bool.true)))))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) _v5) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (@Decidable.byContradiction (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) _v5)
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))
  (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 _v4) _v5) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (fun (_v15 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) _v5)
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)))) =>
(@CarryWindow.prepared_carry._proof_3 _v1 _v2 _v3 _v4 _v5 _v6 _v9 _v12 _v15)))) (fun (_v15 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))) =>
(@CarryWindow.Target.image _v8 _v3 _v4 _v5 _v6 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v7 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) _v15))))) (@And (∀ (_v15 : (@Nat)),
(∀ (_v16 : (@LE.le.{0} (@Nat) (@instLENat) _v15 _v13)),
(@And (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  _v3 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1
  _v2) (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine
  _v0)) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CarryWindow.machine _v0) _v1 _v2 _v15 _v14)))) (@LE.le.{0}
  (@Nat) (@instLENat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)) _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CarryWindow.machine _v0) _v1 _v2 _v15 _v14))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))
  _v4)) _v5) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))))))) (∀ (_v15 : (@Nat)),
(∀ (_v16 : (@LE.le.{0} (@Nat) (@instLENat) _v15 _v13)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))
  _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CarryWindow.machine _v0) _v1 _v2 _v15 _v14))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@CarryWindow.machine _v0))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)) _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CarryWindow.machine _v0) _v1 _v2 _v15 _v14))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@CarryWindow.machine _v0))))))))))))))))))))))) := by
  exact @CarryWindow.prepared_carry

-- Complete literal proposition for CarryWindow.prepared_carry; original proof reused.
theorem PartACanonical.Surface.m0180 :
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
(∀ (_v9 : (@LE.le.{0} (@Nat) (@instLENat) _v6 _v4)),
(∀ (_v10 : (∀ (_v10 : (@Nat)),
(∀ (_v11 : (@LE.le.{0} (@Nat) (@instLENat) _v10 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v8 (@CarryWindow.prepared_carry.match_1.{(0 + 1)} (fun (_v12 : (@Nat)) =>
(@Nat)) _v10 (fun (_v12 : (@Unit)) =>
(@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (fun (_v12 : (@Unit)) =>
(@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))
  (fun (_v12 : (@Unit)) =>
(@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 _v4) _v5) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))) (fun (_v12 : (@Unit)) =>
(@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)) _v5) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))
  (fun (_v12 : (@Unit)) =>
(@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v4)) _v5) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))
  (fun (_v12 : (@Unit)) =>
(@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v4)) _v5) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))
  (fun (_v12 : (@Nat)) =>
(@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v4)) _v5) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))))))
  (@Option.none.{0} (@Bool)))))),
(∀ (_v11 : (∀ (_v11 : (@Nat)),
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4)
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v11)),
(∀ (_v13 : (@LT.lt.{0} (@Nat) (@instLTNat) _v11 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) _v5) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))))),
(@Exists.{(0 + 1)} (@Bool) (fun (_v14 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v8 _v11) (@Option.some.{0} (@Bool) _v14)))))))),
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v4)) _v5) (@OfNat.ofNat.{0} (@Nat)
  (7 : Nat) (@instOfNatNat (7 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))),
(let _v13 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) _v6
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v6) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v4)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v5))
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v4)) (@HMul.hMul.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))) _v5)) (@OfNat.ofNat.{0} (@Nat) (10 : Nat) (@instOfNatNat (10 : Nat))));
(let _v14 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine
  _v0)) _v1 _v2) := (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@CarryWindow.machine _v0)) _v1 _v2 (@CarryWindow.embed _v0 (@VirtualLeaf.embed _v0
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@IngressRepair.producer) (@Cursor.machine _v0) (@Cursor.q _v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (430 : Nat)
  (@instOfNatNat (430 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (93 : Nat) (@instOfNatNat (93 : Nat))) _v0)))))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) _v5) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (@Decidable.byContradiction (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) _v5)
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))
  (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 _v4) _v5) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (fun (_v14 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) _v5)
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)))) =>
(@CarryWindow.prepared_carry._proof_3 _v1 _v2 _v3 _v4 _v5 _v6 _v9 _v12 _v14)))) (fun (_v14 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))) =>
(@CarryWindow.Target.image _v8 _v3 _v4 _v5 _v4 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v6 _v7
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)
  _v14))));
(@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@CarryWindow.machine _v0)) _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CarryWindow.machine _v0) _v1 _v2 _v13
  _v14) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine
  _v0)) _v1 _v2 (@CarryWindow.extra _v0 (@Fin.mk (@OfNat.ofNat.{0} (@Nat) (25 : Nat) (@instOfNatNat (25 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (23 : Nat) (@instOfNatNat (23 : Nat))) (@of_decide_eq_true (@LT.lt.{0} (@Nat) (@instLTNat)
  (@OfNat.ofNat.{0} (@Nat) (23 : Nat) (@instOfNatNat (23 : Nat))) (@OfNat.ofNat.{0} (@Nat) (25 : Nat) (@instOfNatNat (25 :
  Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (23 : Nat) (@instOfNatNat (23 : Nat))) (@OfNat.ofNat.{0} (@Nat) (25 : Nat)
  (@instOfNatNat (25 : Nat)))) (@id.{0} (@Eq.{(0 + 1)} (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat) (@instLTNat)
  (@OfNat.ofNat.{0} (@Nat) (23 : Nat) (@instOfNatNat (23 : Nat))) (@OfNat.ofNat.{0} (@Nat) (25 : Nat) (@instOfNatNat (25 :
  Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (23 : Nat) (@instOfNatNat (23 : Nat))) (@OfNat.ofNat.{0} (@Nat) (25 : Nat)
  (@instOfNatNat (25 : Nat))))) (@Bool.true)) (@Eq.refl.{(0 + 1)} (@Bool) (@Bool.true)))))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) _v5) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (@Decidable.byContradiction (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) _v5)
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))
  (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 _v4) _v5) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (fun (_v15 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) _v5)
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)))) =>
(@CarryWindow.prepared_carry._proof_3 _v1 _v2 _v3 _v4 _v5 _v6 _v9 _v12 _v15)))) (fun (_v15 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))) =>
(@CarryWindow.Target.image _v8 _v3 _v4 _v5 _v6 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v7 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) _v15))))) (@And (∀ (_v15 : (@Nat)),
(∀ (_v16 : (@LE.le.{0} (@Nat) (@instLENat) _v15 _v13)),
(@And (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  _v3 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1
  _v2) (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine
  _v0)) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CarryWindow.machine _v0) _v1 _v2 _v15 _v14)))) (@LE.le.{0}
  (@Nat) (@instLENat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)) _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CarryWindow.machine _v0) _v1 _v2 _v15 _v14))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))
  _v4)) _v5) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))))))) (∀ (_v15 : (@Nat)),
(∀ (_v16 : (@LE.le.{0} (@Nat) (@instLENat) _v15 _v13)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))
  _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CarryWindow.machine _v0) _v1 _v2 _v15 _v14))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@CarryWindow.machine _v0))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)) _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CarryWindow.machine _v0) _v1 _v2 _v15 _v14))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@CarryWindow.machine _v0))))))))))))))))))))))) := by
  exact @CarryWindow.prepared_carry

-- Independent literal expected type for CarryWindow.projection_normal_accepted.
noncomputable def PartACanonical.Types.p0287 :
(let _v0 : (@Pnp3.Complexity.Uniform.V1.Bitstring (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat)))) :=
  (fun (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))))) =>
(@Bool.or (@Bool.or (@Bool.or (@Bool.or (@Bool.or (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat)
  (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))) _v0) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat)
  (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))) _v0) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat)
  (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))) _v0) (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat)
  (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))) _v0) (@OfNat.ofNat.{0}
  (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat)
  (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))) _v0) (@OfNat.ofNat.{0}
  (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat)
  (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))) _v0) (@OfNat.ofNat.{0}
  (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))));
(let _v1 : (@Pnp3.Complexity.Uniform.V1.Bitstring (@OfNat.ofNat.{0} (@Nat) (14 : Nat) (@instOfNatNat (14 : Nat)))) :=
  (fun (_v1 : (@Fin (@OfNat.ofNat.{0} (@Nat) (14 : Nat) (@instOfNatNat (14 : Nat))))) =>
(@Bool.false));
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (14 : Nat) (@instOfNatNat (14 : Nat))) _v0 _v1) (@Bool.true)))) := by
  exact @CarryWindow.projection_normal_accepted

-- Complete literal proposition for CarryWindow.projection_normal_accepted; original proof reused.
theorem PartACanonical.Surface.m0181 :
(let _v0 : (@Pnp3.Complexity.Uniform.V1.Bitstring (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat)))) :=
  (fun (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))))) =>
(@Bool.or (@Bool.or (@Bool.or (@Bool.or (@Bool.or (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat)
  (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))) _v0) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat)
  (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))) _v0) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat)
  (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))) _v0) (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat)
  (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))) _v0) (@OfNat.ofNat.{0}
  (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat)
  (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))) _v0) (@OfNat.ofNat.{0}
  (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat)
  (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))) _v0) (@OfNat.ofNat.{0}
  (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))));
(let _v1 : (@Pnp3.Complexity.Uniform.V1.Bitstring (@OfNat.ofNat.{0} (@Nat) (14 : Nat) (@instOfNatNat (14 : Nat)))) :=
  (fun (_v1 : (@Fin (@OfNat.ofNat.{0} (@Nat) (14 : Nat) (@instOfNatNat (14 : Nat))))) =>
(@Bool.false));
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (14 : Nat) (@instOfNatNat (14 : Nat))) _v0 _v1) (@Bool.true)))) := by
  exact @CarryWindow.projection_normal_accepted

-- Independent literal expected type for CarryWindow.projection_raw_carry.
noncomputable def PartACanonical.Types.p0288 :
(let _v0 : (@Pnp3.Complexity.Uniform.V1.Bitstring (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat)))) :=
  (fun (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))))) =>
(@Bool.or (@Bool.or (@Bool.or (@Bool.or (@Bool.or (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat)
  (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))) _v0) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat)
  (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))) _v0) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat)
  (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))) _v0) (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat)
  (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))) _v0) (@OfNat.ofNat.{0}
  (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat)
  (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))) _v0) (@OfNat.ofNat.{0}
  (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat)
  (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))) _v0) (@OfNat.ofNat.{0}
  (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))));
(let _v1 : (@Pnp3.Complexity.Uniform.V1.Bitstring (@OfNat.ofNat.{0} (@Nat) (14 : Nat) (@instOfNatNat (14 : Nat)))) :=
  (fun (_v1 : (@Fin (@OfNat.ofNat.{0} (@Nat) (14 : Nat) (@instOfNatNat (14 : Nat))))) =>
(@Bool.false));
(@Exists.{(0 + 1)} (@Nat) (fun (_v2 : (@Nat)) =>
(@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine (@OfNat.ofNat.{0} (@Nat) (0
  : Nat) (@instOfNatNat (0 : Nat)))))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (13 : Nat)
  (@instOfNatNat (13 : Nat))) (@OfNat.ofNat.{0} (@Nat) (14 : Nat) (@instOfNatNat (14 : Nat)))) (@OfNat.ofNat.{0} (@Nat)
  (28224 : Nat) (@instOfNatNat (28224 : Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CarryWindow.machine
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))) (@OfNat.ofNat.{0} (@Nat) (14 : Nat) (@instOfNatNat (14 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (28224 : Nat) (@instOfNatNat (28224 : Nat))) _v2
  (@Pnp3.Complexity.Uniform.V1.initialConfig (@CarryWindow.machine (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (14 : Nat) (@instOfNatNat (14 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (28224 : Nat)
  (@instOfNatNat (28224 : Nat))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair (@OfNat.ofNat.{0} (@Nat) (13 : Nat)
  (@instOfNatNat (13 : Nat))) (@OfNat.ofNat.{0} (@Nat) (14 : Nat) (@instOfNatNat (14 : Nat))) _v0 _v1))))
  (@CarryWindow.extra (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Fin.mk (@OfNat.ofNat.{0} (@Nat) (25
  : Nat) (@instOfNatNat (25 : Nat))) (@OfNat.ofNat.{0} (@Nat) (23 : Nat) (@instOfNatNat (23 : Nat))) (@of_decide_eq_true
  (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (23 : Nat) (@instOfNatNat (23 : Nat))) (@OfNat.ofNat.{0} (@Nat)
  (25 : Nat) (@instOfNatNat (25 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (23 : Nat) (@instOfNatNat (23 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (25 : Nat) (@instOfNatNat (25 : Nat)))) (@id.{0} (@Eq.{(0 + 1)} (@Bool) (@Decidable.decide
  (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (23 : Nat) (@instOfNatNat (23 : Nat))) (@OfNat.ofNat.{0} (@Nat)
  (25 : Nat) (@instOfNatNat (25 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (23 : Nat) (@instOfNatNat (23 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (25 : Nat) (@instOfNatNat (25 : Nat))))) (@Bool.true)) (@Eq.refl.{(0 + 1)} (@Bool)
  (@Bool.true))))))))))) := by
  exact @CarryWindow.projection_raw_carry

-- Complete literal proposition for CarryWindow.projection_raw_carry; original proof reused.
theorem PartACanonical.Surface.m0182 :
(let _v0 : (@Pnp3.Complexity.Uniform.V1.Bitstring (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat)))) :=
  (fun (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))))) =>
(@Bool.or (@Bool.or (@Bool.or (@Bool.or (@Bool.or (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat)
  (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))) _v0) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat)
  (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))) _v0) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat)
  (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))) _v0) (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat)
  (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))) _v0) (@OfNat.ofNat.{0}
  (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat)
  (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))) _v0) (@OfNat.ofNat.{0}
  (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat)
  (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))) _v0) (@OfNat.ofNat.{0}
  (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))));
(let _v1 : (@Pnp3.Complexity.Uniform.V1.Bitstring (@OfNat.ofNat.{0} (@Nat) (14 : Nat) (@instOfNatNat (14 : Nat)))) :=
  (fun (_v1 : (@Fin (@OfNat.ofNat.{0} (@Nat) (14 : Nat) (@instOfNatNat (14 : Nat))))) =>
(@Bool.false));
(@Exists.{(0 + 1)} (@Nat) (fun (_v2 : (@Nat)) =>
(@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine (@OfNat.ofNat.{0} (@Nat) (0
  : Nat) (@instOfNatNat (0 : Nat)))))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (13 : Nat)
  (@instOfNatNat (13 : Nat))) (@OfNat.ofNat.{0} (@Nat) (14 : Nat) (@instOfNatNat (14 : Nat)))) (@OfNat.ofNat.{0} (@Nat)
  (28224 : Nat) (@instOfNatNat (28224 : Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CarryWindow.machine
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 : Nat))) (@OfNat.ofNat.{0} (@Nat) (14 : Nat) (@instOfNatNat (14 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (28224 : Nat) (@instOfNatNat (28224 : Nat))) _v2
  (@Pnp3.Complexity.Uniform.V1.initialConfig (@CarryWindow.machine (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (13 : Nat) (@instOfNatNat (13 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (14 : Nat) (@instOfNatNat (14 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (28224 : Nat)
  (@instOfNatNat (28224 : Nat))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair (@OfNat.ofNat.{0} (@Nat) (13 : Nat)
  (@instOfNatNat (13 : Nat))) (@OfNat.ofNat.{0} (@Nat) (14 : Nat) (@instOfNatNat (14 : Nat))) _v0 _v1))))
  (@CarryWindow.extra (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Fin.mk (@OfNat.ofNat.{0} (@Nat) (25
  : Nat) (@instOfNatNat (25 : Nat))) (@OfNat.ofNat.{0} (@Nat) (23 : Nat) (@instOfNatNat (23 : Nat))) (@of_decide_eq_true
  (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (23 : Nat) (@instOfNatNat (23 : Nat))) (@OfNat.ofNat.{0} (@Nat)
  (25 : Nat) (@instOfNatNat (25 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (23 : Nat) (@instOfNatNat (23 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (25 : Nat) (@instOfNatNat (25 : Nat)))) (@id.{0} (@Eq.{(0 + 1)} (@Bool) (@Decidable.decide
  (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (23 : Nat) (@instOfNatNat (23 : Nat))) (@OfNat.ofNat.{0} (@Nat)
  (25 : Nat) (@instOfNatNat (25 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (23 : Nat) (@instOfNatNat (23 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (25 : Nat) (@instOfNatNat (25 : Nat))))) (@Bool.true)) (@Eq.refl.{(0 + 1)} (@Bool)
  (@Bool.true))))))))))) := by
  exact @CarryWindow.projection_raw_carry

-- Independent literal expected type for CarryWindow.raw_carry.
noncomputable def PartACanonical.Types.p0289 :
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
(let _v22 : (∀ (_v22 : (@Nat)),
(@Option.{0} (@Bool))) := (@CappedWeight.Target.image _v21 _v13 _v12 _v14 _v16 (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) _v12 _v0) _v0) (@Cursor.Target.W _v0 _v12) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))));
(let _v23 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11) := (@Pnp3.Complexity.Uniform.V1.initialConfig
  (@CarryWindow.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4));
(∀ (_v24 : (@LT.lt.{0} (@Nat) (@instLTNat) _v15 _v9)),
(∀ (_v25 : (@LE.le.{0} (@Nat) (@instLENat) (@Pnp4.Frontier.ContractExpansion.bitLength _v12) _v16)),
(∀ (_v26 : (@LE.le.{0} (@Nat) (@instLENat) (@Cursor.Target.W _v0 _v12) _v16)),
(@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v16)) _v12) (@OfNat.ofNat.{0}
  (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11)) (fun (_v27 :
  (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v16)) _v12) (@OfNat.ofNat.{0} (@Nat) (7 :
  Nat) (@instOfNatNat (7 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11))) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v28 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v28 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (268435456 : Nat) (@instOfNatNat (268435456 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (let _v29 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat)
  (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v12 _v0) _v0);
(let _v30 : (@Nat) := (@Cursor.Target.W _v0 _v12);
(let _v31 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) _v29
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v29) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v16)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v12))
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v16))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v12)) (@OfNat.ofNat.{0} (@Nat) (10 : Nat) (@instOfNatNat (10 : Nat))));
(@And (@LE.le.{0} (@Nat) (@instLENat) _v31 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (1048576 : Nat) (@instOfNatNat (1048576 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))))) (@And (@Eq.{(0 + 1)}
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@CarryWindow.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v28 _v23)
  (@CarryWindow.config _v0 _v10 _v11 (@VirtualLeaf.config _v0 _v10 _v11
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@IngressRepair.producer) (@Cursor.machine _v0) _v10 _v11
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0)) _v10
  _v11 (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0}
  (@Nat) (430 : Nat) (@instOfNatNat (430 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (93 : Nat) (@instOfNatNat (93 : Nat))) _v0))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 _v16) _v12) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (@lt_of_le_of_lt.{0} (@Nat) (@Nat.instPreorder) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 _v16) _v12) (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v16)) _v12) (@OfNat.ofNat.{0}
  (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11)
  (@Decidable.byContradiction (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 _v16) _v12) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v16)) _v12) (@OfNat.ofNat.{0} (@Nat) (7 :
  Nat) (@instOfNatNat (7 : Nat))))) (@Nat.decLe (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 _v16) _v12) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v16)) _v12) (@OfNat.ofNat.{0} (@Nat) (7 :
  Nat) (@instOfNatNat (7 : Nat))))) (fun (_v32 : (@Not (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 _v16) _v12)
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v16)) _v12)
  (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))))) =>
(@CarryWindow.raw_carry._proof_1 _v0 _v1 _v2 _v6 _v7 _v32))) _v27)) (fun (_v32 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11))) =>
(@_v22 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11) _v32)))))))) (@And (∀ (_v32 : (@Nat)),
(∀ (_v33 : (@LT.lt.{0} (@Nat) (@instLTNat) _v32 _v28)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@CarryWindow.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v32 _v23))
  (@CarryWindow.embed _v0 (@VirtualLeaf.embed _v0 (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight
  (@IngressRepair.producer) (@Cursor.machine _v0) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (430 : Nat) (@instOfNatNat (430 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (93 : Nat) (@instOfNatNat (93 : Nat)))
  _v0))))))))) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@CarryWindow.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CarryWindow.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v28 _v31) _v23) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@CarryWindow.extra _v0 (@Fin.mk (@OfNat.ofNat.{0}
  (@Nat) (25 : Nat) (@instOfNatNat (25 : Nat))) (@OfNat.ofNat.{0} (@Nat) (23 : Nat) (@instOfNatNat (23 : Nat)))
  (@of_decide_eq_true (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (23 : Nat) (@instOfNatNat (23 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (25 : Nat) (@instOfNatNat (25 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (23 : Nat)
  (@instOfNatNat (23 : Nat))) (@OfNat.ofNat.{0} (@Nat) (25 : Nat) (@instOfNatNat (25 : Nat)))) (@id.{0} (@Eq.{(0 + 1)}
  (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (23 : Nat) (@instOfNatNat (23 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (25 : Nat) (@instOfNatNat (25 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (23 : Nat)
  (@instOfNatNat (23 : Nat))) (@OfNat.ofNat.{0} (@Nat) (25 : Nat) (@instOfNatNat (25 : Nat))))) (@Bool.true))
  (@Eq.refl.{(0 + 1)} (@Bool) (@Bool.true)))))) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 _v16) _v12) (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@lt_of_le_of_lt.{0} (@Nat) (@Nat.instPreorder) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 _v16) _v12)
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v16)) _v12)
  (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11) (@Decidable.byContradiction (@LE.le.{0} (@Nat)
  (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v14 _v16) _v12) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat)
  (@instOfNatNat (5 : Nat))) _v16)) _v12) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))) (@Nat.decLe
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v14 _v16) _v12) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat)
  (@instOfNatNat (5 : Nat))) _v16)) _v12) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))) (fun (_v32 :
  (@Not (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 _v16) _v12) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 :
  Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v14 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v16)) _v12) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 :
  Nat))))))) =>
(@CarryWindow.raw_carry._proof_1 _v0 _v1 _v2 _v6 _v7 _v32))) _v27)) (fun (_v32 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11))) =>
(@CarryWindow.Target.image _v22 _v14 _v16 _v12 _v29 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v30 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0
  : Nat))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  _v11) _v32))))) (∀ (_v32 : (@Nat)),
(∀ (_v33 : (@LE.le.{0} (@Nat) (@instLENat) _v32 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v28 _v31))),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@CarryWindow.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v32 _v23))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@CarryWindow.machine _v0))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@CarryWindow.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v32 _v23))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@CarryWindow.machine
  _v0)))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @CarryWindow.raw_carry

-- Complete literal proposition for CarryWindow.raw_carry; original proof reused.
theorem PartACanonical.Surface.m0183 :
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
(let _v22 : (∀ (_v22 : (@Nat)),
(@Option.{0} (@Bool))) := (@CappedWeight.Target.image _v21 _v13 _v12 _v14 _v16 (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) _v12 _v0) _v0) (@Cursor.Target.W _v0 _v12) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))));
(let _v23 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11) := (@Pnp3.Complexity.Uniform.V1.initialConfig
  (@CarryWindow.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4));
(∀ (_v24 : (@LT.lt.{0} (@Nat) (@instLTNat) _v15 _v9)),
(∀ (_v25 : (@LE.le.{0} (@Nat) (@instLENat) (@Pnp4.Frontier.ContractExpansion.bitLength _v12) _v16)),
(∀ (_v26 : (@LE.le.{0} (@Nat) (@instLENat) (@Cursor.Target.W _v0 _v12) _v16)),
(@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v16)) _v12) (@OfNat.ofNat.{0}
  (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11)) (fun (_v27 :
  (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v16)) _v12) (@OfNat.ofNat.{0} (@Nat) (7 :
  Nat) (@instOfNatNat (7 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11))) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v28 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v28 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (268435456 : Nat) (@instOfNatNat (268435456 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (let _v29 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat)
  (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v12 _v0) _v0);
(let _v30 : (@Nat) := (@Cursor.Target.W _v0 _v12);
(let _v31 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) _v29
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v29) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v16)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v12))
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v16))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v12)) (@OfNat.ofNat.{0} (@Nat) (10 : Nat) (@instOfNatNat (10 : Nat))));
(@And (@LE.le.{0} (@Nat) (@instLENat) _v31 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (1048576 : Nat) (@instOfNatNat (1048576 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))))) (@And (@Eq.{(0 + 1)}
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@CarryWindow.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v28 _v23)
  (@CarryWindow.config _v0 _v10 _v11 (@VirtualLeaf.config _v0 _v10 _v11
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@IngressRepair.producer) (@Cursor.machine _v0) _v10 _v11
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0)) _v10
  _v11 (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0}
  (@Nat) (430 : Nat) (@instOfNatNat (430 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (93 : Nat) (@instOfNatNat (93 : Nat))) _v0))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 _v16) _v12) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (@lt_of_le_of_lt.{0} (@Nat) (@Nat.instPreorder) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 _v16) _v12) (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v16)) _v12) (@OfNat.ofNat.{0}
  (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11)
  (@Decidable.byContradiction (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 _v16) _v12) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v16)) _v12) (@OfNat.ofNat.{0} (@Nat) (7 :
  Nat) (@instOfNatNat (7 : Nat))))) (@Nat.decLe (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 _v16) _v12) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v16)) _v12) (@OfNat.ofNat.{0} (@Nat) (7 :
  Nat) (@instOfNatNat (7 : Nat))))) (fun (_v32 : (@Not (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 _v16) _v12)
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v16)) _v12)
  (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))))) =>
(@CarryWindow.raw_carry._proof_1 _v0 _v1 _v2 _v6 _v7 _v32))) _v27)) (fun (_v32 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11))) =>
(@_v22 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11) _v32)))))))) (@And (∀ (_v32 : (@Nat)),
(∀ (_v33 : (@LT.lt.{0} (@Nat) (@instLTNat) _v32 _v28)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@CarryWindow.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v32 _v23))
  (@CarryWindow.embed _v0 (@VirtualLeaf.embed _v0 (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight
  (@IngressRepair.producer) (@Cursor.machine _v0) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (430 : Nat) (@instOfNatNat (430 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (93 : Nat) (@instOfNatNat (93 : Nat)))
  _v0))))))))) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@CarryWindow.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CarryWindow.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v28 _v31) _v23) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@CarryWindow.extra _v0 (@Fin.mk (@OfNat.ofNat.{0}
  (@Nat) (25 : Nat) (@instOfNatNat (25 : Nat))) (@OfNat.ofNat.{0} (@Nat) (23 : Nat) (@instOfNatNat (23 : Nat)))
  (@of_decide_eq_true (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (23 : Nat) (@instOfNatNat (23 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (25 : Nat) (@instOfNatNat (25 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (23 : Nat)
  (@instOfNatNat (23 : Nat))) (@OfNat.ofNat.{0} (@Nat) (25 : Nat) (@instOfNatNat (25 : Nat)))) (@id.{0} (@Eq.{(0 + 1)}
  (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (23 : Nat) (@instOfNatNat (23 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (25 : Nat) (@instOfNatNat (25 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (23 : Nat)
  (@instOfNatNat (23 : Nat))) (@OfNat.ofNat.{0} (@Nat) (25 : Nat) (@instOfNatNat (25 : Nat))))) (@Bool.true))
  (@Eq.refl.{(0 + 1)} (@Bool) (@Bool.true)))))) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 _v16) _v12) (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@lt_of_le_of_lt.{0} (@Nat) (@Nat.instPreorder) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 _v16) _v12)
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v16)) _v12)
  (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11) (@Decidable.byContradiction (@LE.le.{0} (@Nat)
  (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v14 _v16) _v12) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat)
  (@instOfNatNat (5 : Nat))) _v16)) _v12) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))) (@Nat.decLe
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v14 _v16) _v12) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat)
  (@instOfNatNat (5 : Nat))) _v16)) _v12) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))) (fun (_v32 :
  (@Not (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 _v16) _v12) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 :
  Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v14 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v16)) _v12) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 :
  Nat))))))) =>
(@CarryWindow.raw_carry._proof_1 _v0 _v1 _v2 _v6 _v7 _v32))) _v27)) (fun (_v32 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11))) =>
(@CarryWindow.Target.image _v22 _v14 _v16 _v12 _v29 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v30 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0
  : Nat))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  _v11) _v32))))) (∀ (_v32 : (@Nat)),
(∀ (_v33 : (@LE.le.{0} (@Nat) (@instLENat) _v32 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v28 _v31))),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@CarryWindow.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v32 _v23))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@CarryWindow.machine _v0))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@CarryWindow.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v32 _v23))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@CarryWindow.machine
  _v0)))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @CarryWindow.raw_carry

-- Independent literal expected type for CarryWindow.ready.
noncomputable def PartACanonical.Types.p0290 :
(∀ (_v0 : (@Nat)),
(@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)))) := by
  exact @CarryWindow.ready

-- Independent literal expected type for CarryWindow.repair138.
noncomputable def PartACanonical.Types.p0291 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step
  (@CarryWindow.machine _v0) (@CarryWindow.embed _v0 (@VirtualLeaf.embed _v0
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqLeft (@IngressRepair.producer) (@Cursor.machine _v0) (@SmallIngress.q
  (@OfNat.ofNat.{0} (@Nat) (138 : Nat) (@instOfNatNat (138 : Nat))))))) (@Option.none.{0} (@Bool))) (@Prod.mk.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@CarryWindow.machine _v0))
  (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.none.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move.stay))))) := by
  exact @CarryWindow.repair138

-- Complete literal proposition for CarryWindow.repair138; original proof reused.
theorem PartACanonical.Surface.m0184 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step
  (@CarryWindow.machine _v0) (@CarryWindow.embed _v0 (@VirtualLeaf.embed _v0
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqLeft (@IngressRepair.producer) (@Cursor.machine _v0) (@SmallIngress.q
  (@OfNat.ofNat.{0} (@Nat) (138 : Nat) (@instOfNatNat (138 : Nat))))))) (@Option.none.{0} (@Bool))) (@Prod.mk.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@CarryWindow.machine _v0))
  (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.none.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move.stay))))) := by
  exact @CarryWindow.repair138

-- Independent literal expected type for CarryWindow.stall_reject.
noncomputable def PartACanonical.Types.p0292 :
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
(let _v2 : (@Pnp3.Complexity.Uniform.V1.Bitstring (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) :=
  (@Fin.elim0.{(0 + 1)} (@Bool));
(@Exists.{(0 + 1)} (@Nat) (fun (_v3 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (128 : Nat) (@instOfNatNat (128 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat)))))) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CarryWindow.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) _v3 (@Pnp3.Complexity.Uniform.V1.initialConfig (@CarryWindow.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat
  (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v1 _v2))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@CarryWindow.machine _v0))) (@Eq.{(0 + 1)} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v1 _v2) (@Bool.false))))))))) := by
  exact @CarryWindow.stall_reject

-- Complete literal proposition for CarryWindow.stall_reject; original proof reused.
theorem PartACanonical.Surface.m0185 :
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
(let _v2 : (@Pnp3.Complexity.Uniform.V1.Bitstring (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) :=
  (@Fin.elim0.{(0 + 1)} (@Bool));
(@Exists.{(0 + 1)} (@Nat) (fun (_v3 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (128 : Nat) (@instOfNatNat (128 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat)))))) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CarryWindow.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) _v3 (@Pnp3.Complexity.Uniform.V1.initialConfig (@CarryWindow.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat
  (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v1 _v2))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@CarryWindow.machine _v0))) (@Eq.{(0 + 1)} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v1 _v2) (@Bool.false))))))))) := by
  exact @CarryWindow.stall_reject

-- Independent literal expected type for CarryWindow.table_delta.
noncomputable def PartACanonical.Types.p0293 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0)))),
(∀ (_v2 : (@Option.{0} (@Bool))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step
  (@CarryWindow.machine _v0) (@CarryWindow.embed _v0 _v1) _v2) (@ite.{(0 + 1)} (@Prod.{0, 0} (@Fin (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@CanonicalLeaf.machine _v0)) (@OfNat.ofNat.{0} (@Nat) (25 : Nat) (@instOfNatNat (25 : Nat))))) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@And (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0))) _v1 (@VirtualLeaf.embed _v0
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@IngressRepair.producer) (@Cursor.machine _v0) (@Cursor.q _v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (430 : Nat)
  (@instOfNatNat (430 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (93 : Nat) (@instOfNatNat (93 : Nat))) _v0)))))) (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) _v2
  (@Option.none.{0} (@Bool)))) (@instDecidableAnd (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@CanonicalLeaf.machine _v0))) _v1 (@VirtualLeaf.embed _v0 (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight
  (@IngressRepair.producer) (@Cursor.machine _v0) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (430 : Nat) (@instOfNatNat (430 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (93 : Nat) (@instOfNatNat (93 : Nat)))
  _v0)))))) (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) _v2 (@Option.none.{0} (@Bool))) (@instDecidableEqFin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0)) _v1 (@VirtualLeaf.embed _v0
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@IngressRepair.producer) (@Cursor.machine _v0) (@Cursor.q _v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (430 : Nat)
  (@instOfNatNat (430 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (93 : Nat) (@instOfNatNat (93 : Nat))) _v0)))))) (@Option.instDecidableEq.{0} (@Bool)
  (@instDecidableEqBool) _v2 (@Option.none.{0} (@Bool)))) (@Prod.mk.{0, 0} (@Fin (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine
  _v0)) (@OfNat.ofNat.{0} (@Nat) (25 : Nat) (@instOfNatNat (25 : Nat))))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@CarryWindow.extra _v0 (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (25 : Nat)
  (@instOfNatNat (25 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (25 : Nat) (@instOfNatNat (25 : Nat)))
  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (24 : Nat) (@instOfNatNat (24 : Nat)))) (0 : Nat)))) (@Prod.mk.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.none.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move.left))) (@ite.{(0 + 1)} (@Prod.{0, 0} (@Fin (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0))
  (@OfNat.ofNat.{0} (@Nat) (25 : Nat) (@instOfNatNat (25 : Nat))))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@CanonicalLeaf.machine _v0))) _v1 (@VirtualLeaf.embed _v0 (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight
  (@IngressRepair.producer) (@Cursor.machine _v0) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (613 : Nat) (@instOfNatNat (613 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (93 : Nat) (@instOfNatNat (93 : Nat)))
  _v0)))))) (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) _v2 (@Option.none.{0} (@Bool)))) (@instDecidableAnd (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0))) _v1 (@VirtualLeaf.embed _v0
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@IngressRepair.producer) (@Cursor.machine _v0) (@Cursor.q _v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (613 : Nat)
  (@instOfNatNat (613 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (93 : Nat) (@instOfNatNat (93 : Nat))) _v0)))))) (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) _v2
  (@Option.none.{0} (@Bool))) (@instDecidableEqFin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@CanonicalLeaf.machine _v0)) _v1 (@VirtualLeaf.embed _v0 (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight
  (@IngressRepair.producer) (@Cursor.machine _v0) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (613 : Nat) (@instOfNatNat (613 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (93 : Nat) (@instOfNatNat (93 : Nat)))
  _v0)))))) (@Option.instDecidableEq.{0} (@Bool) (@instDecidableEqBool) _v2 (@Option.none.{0} (@Bool)))) (@Prod.mk.{0, 0}
  (@Fin (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0)) (@OfNat.ofNat.{0} (@Nat) (25 : Nat)
  (@instOfNatNat (25 : Nat))))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))
  (@CarryWindow.ready _v0) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.none.{0}
  (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move.stay))) (@Prod.mk.{0, 0} (@Fin (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0))
  (@OfNat.ofNat.{0} (@Nat) (25 : Nat) (@instOfNatNat (25 : Nat))))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@CarryWindow.embed _v0 (@Prod.fst.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@CanonicalLeaf.machine _v0) _v1 _v2)))
  (@Prod.snd.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0))) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step
  (@CanonicalLeaf.machine _v0) _v1 _v2))))))))) := by
  exact @CarryWindow.table_delta

-- Complete literal proposition for CarryWindow.table_delta; original proof reused.
theorem PartACanonical.Surface.m0186 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0)))),
(∀ (_v2 : (@Option.{0} (@Bool))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step
  (@CarryWindow.machine _v0) (@CarryWindow.embed _v0 _v1) _v2) (@ite.{(0 + 1)} (@Prod.{0, 0} (@Fin (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@CanonicalLeaf.machine _v0)) (@OfNat.ofNat.{0} (@Nat) (25 : Nat) (@instOfNatNat (25 : Nat))))) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@And (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0))) _v1 (@VirtualLeaf.embed _v0
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@IngressRepair.producer) (@Cursor.machine _v0) (@Cursor.q _v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (430 : Nat)
  (@instOfNatNat (430 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (93 : Nat) (@instOfNatNat (93 : Nat))) _v0)))))) (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) _v2
  (@Option.none.{0} (@Bool)))) (@instDecidableAnd (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@CanonicalLeaf.machine _v0))) _v1 (@VirtualLeaf.embed _v0 (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight
  (@IngressRepair.producer) (@Cursor.machine _v0) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (430 : Nat) (@instOfNatNat (430 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (93 : Nat) (@instOfNatNat (93 : Nat)))
  _v0)))))) (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) _v2 (@Option.none.{0} (@Bool))) (@instDecidableEqFin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0)) _v1 (@VirtualLeaf.embed _v0
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@IngressRepair.producer) (@Cursor.machine _v0) (@Cursor.q _v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (430 : Nat)
  (@instOfNatNat (430 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (93 : Nat) (@instOfNatNat (93 : Nat))) _v0)))))) (@Option.instDecidableEq.{0} (@Bool)
  (@instDecidableEqBool) _v2 (@Option.none.{0} (@Bool)))) (@Prod.mk.{0, 0} (@Fin (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine
  _v0)) (@OfNat.ofNat.{0} (@Nat) (25 : Nat) (@instOfNatNat (25 : Nat))))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@CarryWindow.extra _v0 (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (25 : Nat)
  (@instOfNatNat (25 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (25 : Nat) (@instOfNatNat (25 : Nat)))
  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (24 : Nat) (@instOfNatNat (24 : Nat)))) (0 : Nat)))) (@Prod.mk.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.none.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move.left))) (@ite.{(0 + 1)} (@Prod.{0, 0} (@Fin (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0))
  (@OfNat.ofNat.{0} (@Nat) (25 : Nat) (@instOfNatNat (25 : Nat))))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@CanonicalLeaf.machine _v0))) _v1 (@VirtualLeaf.embed _v0 (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight
  (@IngressRepair.producer) (@Cursor.machine _v0) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (613 : Nat) (@instOfNatNat (613 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (93 : Nat) (@instOfNatNat (93 : Nat)))
  _v0)))))) (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) _v2 (@Option.none.{0} (@Bool)))) (@instDecidableAnd (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0))) _v1 (@VirtualLeaf.embed _v0
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@IngressRepair.producer) (@Cursor.machine _v0) (@Cursor.q _v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (613 : Nat)
  (@instOfNatNat (613 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (93 : Nat) (@instOfNatNat (93 : Nat))) _v0)))))) (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) _v2
  (@Option.none.{0} (@Bool))) (@instDecidableEqFin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@CanonicalLeaf.machine _v0)) _v1 (@VirtualLeaf.embed _v0 (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight
  (@IngressRepair.producer) (@Cursor.machine _v0) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (613 : Nat) (@instOfNatNat (613 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (93 : Nat) (@instOfNatNat (93 : Nat)))
  _v0)))))) (@Option.instDecidableEq.{0} (@Bool) (@instDecidableEqBool) _v2 (@Option.none.{0} (@Bool)))) (@Prod.mk.{0, 0}
  (@Fin (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0)) (@OfNat.ofNat.{0} (@Nat) (25 : Nat)
  (@instOfNatNat (25 : Nat))))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))
  (@CarryWindow.ready _v0) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.none.{0}
  (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move.stay))) (@Prod.mk.{0, 0} (@Fin (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0))
  (@OfNat.ofNat.{0} (@Nat) (25 : Nat) (@instOfNatNat (25 : Nat))))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@CarryWindow.embed _v0 (@Prod.fst.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@CanonicalLeaf.machine _v0) _v1 _v2)))
  (@Prod.snd.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0))) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step
  (@CanonicalLeaf.machine _v0) _v1 _v2))))))))) := by
  exact @CarryWindow.table_delta

-- Independent literal expected type for CertificateGuardClosure.Audit.check_component_rows.
noncomputable def PartACanonical.Types.p0294 :
(∀ (_v0 : (@Nat)),
(@And (@Function.Injective.{(0 + 1), (0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@TotalIngressClosure.machine _v0))) (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@CertificateGuardClosure.machine _v0))) (@CertificateGuardClosure.old _v0)) (@And (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CertificateGuardClosure.machine _v0))) (@CertificateGuardClosure.old
  _v0 (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@TotalIngressClosure.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@CertificateGuardClosure.machine _v0))) (@And (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CertificateGuardClosure.machine _v0))) (@CertificateGuardClosure.old
  _v0 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@TotalIngressClosure.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@CertificateGuardClosure.machine _v0))) (∀ (_v1 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@TotalIngressClosure.machine _v0)))),
(∀ (_v2 : (@Option.{0} (@Bool))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CertificateGuardClosure.machine
  _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@CertificateGuardClosure.machine _v0) (@CertificateGuardClosure.old _v0
  _v1) _v2) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CertificateGuardClosure.machine
  _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@CertificateGuardClosure.old _v0
  (@Prod.fst.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@TotalIngressClosure.machine _v0)))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step
  (@TotalIngressClosure.machine _v0) _v1 _v2))) (@Prod.snd.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@TotalIngressClosure.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@TotalIngressClosure.machine _v0) _v1 _v2)))))))))) := by
  exact @CertificateGuardClosure.Audit.check_component_rows

-- Complete literal proposition for CertificateGuardClosure.Audit.check_component_rows; original proof reused.
theorem PartACanonical.Surface.m0187 :
(∀ (_v0 : (@Nat)),
(@And (@Function.Injective.{(0 + 1), (0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@TotalIngressClosure.machine _v0))) (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@CertificateGuardClosure.machine _v0))) (@CertificateGuardClosure.old _v0)) (@And (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CertificateGuardClosure.machine _v0))) (@CertificateGuardClosure.old
  _v0 (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@TotalIngressClosure.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@CertificateGuardClosure.machine _v0))) (@And (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CertificateGuardClosure.machine _v0))) (@CertificateGuardClosure.old
  _v0 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@TotalIngressClosure.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@CertificateGuardClosure.machine _v0))) (∀ (_v1 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@TotalIngressClosure.machine _v0)))),
(∀ (_v2 : (@Option.{0} (@Bool))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CertificateGuardClosure.machine
  _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@CertificateGuardClosure.machine _v0) (@CertificateGuardClosure.old _v0
  _v1) _v2) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CertificateGuardClosure.machine
  _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@CertificateGuardClosure.old _v0
  (@Prod.fst.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@TotalIngressClosure.machine _v0)))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step
  (@TotalIngressClosure.machine _v0) _v1 _v2))) (@Prod.snd.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@TotalIngressClosure.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@TotalIngressClosure.machine _v0) _v1 _v2)))))))))) := by
  exact @CertificateGuardClosure.Audit.check_component_rows

-- Independent literal expected type for CertificateGuardClosure.Audit.check_content_equation.
noncomputable def PartACanonical.Types.p0295 :
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
  exact @CertificateGuardClosure.Audit.check_content_equation

-- Complete literal proposition for CertificateGuardClosure.Audit.check_content_equation; original proof reused.
theorem PartACanonical.Surface.m0188 :
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
  exact @CertificateGuardClosure.Audit.check_content_equation

-- Independent literal expected type for CertificateGuardClosure.Audit.check_raw.
noncomputable def PartACanonical.Types.p0297 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(let _v3 : (@Nat) := (@CertificateGuardClosure.allocation _v0 _v1);
(let _v4 : (@Pnp3.Complexity.Uniform.V1.UniformTM) := (@CertificateGuardClosure.machine _v0);
(let _v5 : (@Pnp3.Complexity.Uniform.V1.UniformTM) := (@TotalIngressClosure.machine _v0);
(let _v6 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v4 _v1 _v3 _v2);
(let _v7 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5) _v1 _v3) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v5 _v1 _v3 _v2);
(@Exists.{(0 + 1)} (@Nat) (fun (_v8 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v8 (@CertificateGuardClosure.deadline _v0 _v1)) (@And (∀ (_v9 : (@Nat)),
(∀ (_v10 : (@LE.le.{0} (@Nat) (@instLENat) _v9 _v8)),
(@LE.le.{0} (@Nat) (@instLENat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3 _v9 _v6))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))) (@HPow.hPow.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))))) (@And (∀ (_v9 : (@Nat)),
(∀ (_v10 : (@LE.le.{0} (@Nat) (@instLENat) _v9 _v8)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3
  _v9 _v6)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v4)))) (@And (∀ (_v9 : (@Nat)),
(∀ (_v10 : (@LT.lt.{0} (@Nat) (@instLTNat) _v9 _v8)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3 _v9 _v6)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v4))
  (@And (∀ (_v11 : (@Bool)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3
  _v9 _v6)) (@CertificateGuardClosure.old _v0 (@TotalIngressClosure.old _v0 (@BodyIngress.old _v0 (@CarryWindow.embed _v0
  (@CanonicalLeaf.result _v0 _v11))))))) (∀ (_v11 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3
  _v9 _v6)) (@CertificateGuardClosure.old _v0 (@TotalIngressClosure.old _v0 (@BodyIngress.body _v0 (@SerializedBody.entry
  _v11)))))))))) (@Or (@And (@Eq.{(0 + 1)} (@Option.{0} (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.decodePair _v1 _v2) (@Option.none.{0}
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))) (@And (@Eq.{(0 + 1)} (@Nat) _v8
  (@Pnp3.Complexity.Uniform.V1.FixedPairParser.clock _v1)) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3
  _v8 _v6) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v4) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3)
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
  (@covariant_swap_add_of_covariant_add.{0} (@Nat) (fun (_v9 : (@Nat)) =>
(fun (_v10 : (@Nat)) =>
(@LE.le.{0} (@Nat) (@Preorder.toLE.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) _v9 _v10)))
  (@Nat.instAddCommSemigroup) (@IsOrderedAddMonoid.toAddLeftMono.{0} (@Nat) (@Nat.instAddCommMonoid)
  (@Nat.instPartialOrder) (@Nat.instIsOrderedAddMonoid)))) (@contravariant_swap_add_of_contravariant_add.{0} (@Nat) (fun
  (_v9 : (@Nat)) =>
(fun (_v10 : (@Nat)) =>
(@LT.lt.{0} (@Nat) (@instLTNat) _v9 _v10))) (@Nat.instAddCommSemigroup) (@contravariant_lt_of_covariant_le.{0} (@Nat)
  (fun (_v9 : (@Nat)) =>
(fun (_v10 : (@Nat)) =>
(@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@AddCommMagma.toAdd.{0} (@Nat)
  (@AddCommSemigroup.toAddCommMagma.{0} (@Nat) (@Nat.instAddCommSemigroup)))) _v9 _v10))) (@Nat.instLinearOrder)
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
  (Sort 0) (∀ (_v9 : (Sort 0)),
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
  (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3 _v6))) (@Eq.{(0
  + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.encodedRelationLanguage
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0) _v1 _v2) (@Bool.false))))) (@Or
  (@Exists.{(0 + 1)} (@Nat) (fun (_v9 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v10 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v9) (fun (_v11 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v9))
  =>
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v10) (fun (_v12 : (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v10)) =>
(@Exists.{0} (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v9 _v10) _v1) (fun (_v13 :
  (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v9 _v10) _v1)) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.decodePair _v1 _v2) (@Option.some.{0} (@Prod.{0, 0} (@Sigma.{0, 0} (@Nat) (fun
  (_v14 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v14))) (@Sigma.{0, 0} (@Nat) (fun (_v14 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v14)))) (@Prod.mk.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v14 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v14))) (@Sigma.{0, 0} (@Nat) (fun (_v14 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v14))) (@Sigma.mk.{0, 0} (@Nat) (fun (_v14 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v14)) _v9 _v11) (@Sigma.mk.{0, 0} (@Nat) (fun (_v14 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v14)) _v10 _v12)))) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v1) _v2 (@Eq.rec.{(0 + 1), (0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v9 _v10) (fun (_v14 :
  (@Nat)) =>
(fun (_v15 : (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v9 _v10) _v14)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v14))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v9 _v10 _v11 _v12)
  _v1 _v13)) (@And (@Ne.{(0 + 1)} (@Nat) _v10 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v9 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@And (@LE.le.{0} (@Nat) (@instLENat)
  _v8 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp3.Complexity.Uniform.V1.FixedPairParser.clock _v1) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))))) (@And (@Eq.{(0 + 1)}
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3 _v8 _v6) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v4)
  (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@of_eq_true (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@AddZeroClass.toAdd.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@Nat.instAddMonoid)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v3)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))))) (@Eq.trans.{(0 + 1)} (Sort 0) (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@AddZeroClass.toAdd.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@Nat.instAddMonoid)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v3)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))))) (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat)
  (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@Nat.instAddMonoid))))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v3) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@True)
  (@lt_mul_iff_one_lt_left'._simp_4.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@Nat.instAddMonoid)) (@instLTNat)
  (@IsRightCancelAdd.addRightStrictMono_of_addRightMono.{0} (@Nat) (@AddZeroClass.toAdd.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@Nat.instAddMonoid))) (@IsCancelAdd.toIsRightCancelAdd.{0} (@Nat)
  (@AddZeroClass.toAdd.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@Nat.instAddMonoid)))
  (@IsOrderedCancelAddMonoid.toIsCancelAdd.{0} (@Nat) (@Nat.instAddCommMonoid) (@Nat.instPartialOrder)
  (@Nat.instIsOrderedCancelAddMonoid))) (@Nat.instPartialOrder) (@covariant_swap_add_of_covariant_add.{0} (@Nat) (fun
  (_v14 : (@Nat)) =>
(fun (_v15 : (@Nat)) =>
(@LE.le.{0} (@Nat) (@Preorder.toLE.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) _v14
  _v15))) (@Nat.instAddCommSemigroup) (@IsOrderedAddMonoid.toAddLeftMono.{0} (@Nat) (@Nat.instAddCommMonoid)
  (@Nat.instPartialOrder) (@Nat.instIsOrderedAddMonoid)))) (@contravariant_swap_add_of_contravariant_add.{0} (@Nat) (fun
  (_v14 : (@Nat)) =>
(fun (_v15 : (@Nat)) =>
(@LT.lt.{0} (@Nat) (@instLTNat) _v14 _v15))) (@Nat.instAddCommSemigroup) (@contravariant_lt_of_covariant_le.{0} (@Nat)
  (fun (_v14 : (@Nat)) =>
(fun (_v15 : (@Nat)) =>
(@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@AddCommMagma.toAdd.{0} (@Nat)
  (@AddCommSemigroup.toAddCommMagma.{0} (@Nat) (@Nat.instAddCommSemigroup)))) _v14 _v15))) (@Nat.instLinearOrder)
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
  (Sort 0) (∀ (_v14 : (Sort 0)),
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
  (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3 _v6))) (@Eq.{(0
  + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v9 _v10 _v11 _v12)
  (@Bool.false))))))))))))))))) (@Exists.{(0 + 1)} (@Nat) (fun (_v9 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v10 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v9) (fun (_v11 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v9))
  =>
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v10) (fun (_v12 : (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v10)) =>
(@Exists.{0} (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v9 _v10) _v1) (fun (_v13 :
  (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v9 _v10) _v1)) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.decodePair _v1 _v2) (@Option.some.{0} (@Prod.{0, 0} (@Sigma.{0, 0} (@Nat) (fun
  (_v14 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v14))) (@Sigma.{0, 0} (@Nat) (fun (_v14 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v14)))) (@Prod.mk.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v14 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v14))) (@Sigma.{0, 0} (@Nat) (fun (_v14 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v14))) (@Sigma.mk.{0, 0} (@Nat) (fun (_v14 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v14)) _v9 _v11) (@Sigma.mk.{0, 0} (@Nat) (fun (_v14 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v14)) _v10 _v12)))) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v1) _v2 (@Eq.rec.{(0 + 1), (0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v9 _v10) (fun (_v14 :
  (@Nat)) =>
(fun (_v15 : (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v9 _v10) _v14)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v14))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v9 _v10 _v11 _v12)
  _v1 _v13)) (@And (@Eq.{(0 + 1)} (@Nat) _v10 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v9 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Exists.{(0 + 1)} (@Nat) (fun (_v14
  : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v15 : (@Nat)) =>
(@And (@Eq.{(0 + 1)} (@Nat) _v8 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14
  _v15)) (@And (@LE.le.{0} (@Nat) (@instLENat) _v14 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.FixedPairParser.clock _v1) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) (@HPow.hPow.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))))) (@And (∀ (_v16 : (@Nat)),
(∀ (_v17 : (@LT.lt.{0} (@Nat) (@instLTNat) _v16 _v14)),
(@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4)
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3 _v16 _v6))) (@OfNat.ofNat.{0} (@Nat) (77 : Nat) (@instOfNatNat
  (77 : Nat)))))) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3
  _v14 _v6) (@CertificateGuardClosure.config _v0 _v1 _v3 _v7)) (@And (∀ (_v16 : (@Nat)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v14 _v16) _v6) (@CertificateGuardClosure.config _v0 _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  _v5 _v1 _v3 _v16 _v7)))) (@And (let _v16 : (@Nat) := (@TotalIngressClosure.allocation _v0 _v1);
(let _v17 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation _v1);
(let _v18 : (@Pnp3.Complexity.Uniform.V1.UniformTM) := (@TotalIngressClosure.machine _v0);
(let _v19 : (@Pnp3.Complexity.Uniform.V1.UniformTM) := (@BodyIngress.machine _v0);
(let _v20 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v18) _v1 _v16) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v18 _v1 _v16 _v2);
(let _v21 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v19) _v1 _v17) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v19 _v1 _v17 _v2);
(let _v22 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v19) _v1 _v16) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v19 _v1 _v16 _v2);
(@And (@LE.le.{0} (@Nat) (@instLENat) _v15 (@TotalIngressClosure.deadline _v0 _v1)) (@And (∀ (_v23 : (@Nat)),
(∀ (_v24 : (@LE.le.{0} (@Nat) (@instLENat) _v23 _v15)),
(@LE.le.{0} (@Nat) (@instLENat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v16)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v18) _v1 _v16
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v18 _v1 _v16 _v23 _v20))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))) (@HPow.hPow.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))))) (@And (∀ (_v23 : (@Nat)),
(∀ (_v24 : (@LE.le.{0} (@Nat) (@instLENat) _v23 _v15)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v18)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v18) _v1 _v16 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v18 _v1
  _v16 _v23 _v20)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v18)))) (@And (∀ (_v23 : (@Nat)),
(∀ (_v24 : (@LT.lt.{0} (@Nat) (@instLTNat) _v23 _v15)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v18))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v18) _v1 _v16
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v18 _v1 _v16 _v23 _v20)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject
  _v18)) (@And (∀ (_v25 : (@Bool)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v18)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v18) _v1 _v16 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v18 _v1
  _v16 _v23 _v20)) (@TotalIngressClosure.old _v0 (@BodyIngress.old _v0 (@CarryWindow.embed _v0 (@CanonicalLeaf.result _v0
  _v25)))))) (∀ (_v25 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v18)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v18) _v1 _v16 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v18 _v1
  _v16 _v23 _v20)) (@TotalIngressClosure.old _v0 (@BodyIngress.body _v0 (@SerializedBody.entry _v25))))))))) (@Or (@And
  (@Eq.{(0 + 1)} (@Option.{0} (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.decodePair _v1 _v2) (@Option.none.{0}
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))) (@And (@Eq.{(0 + 1)} (@Nat) _v15
  (@Pnp3.Complexity.Uniform.V1.FixedPairParser.clock _v1)) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v18) _v1 _v16) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v18 _v1
  _v16 _v15 _v20) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v18) _v1 _v16
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v18) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v16)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@of_eq_true (@LT.lt.{0} (@Nat) (@instLTNat)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@AddZeroClass.toAdd.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@Nat.instAddMonoid)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v16) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat)
  (0 : Nat) (@instOfNatNat (0 : Nat))))) (@Eq.trans.{(0 + 1)} (Sort 0) (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@AddZeroClass.toAdd.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@Nat.instAddMonoid)))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v16) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat)
  (0 : Nat) (@instOfNatNat (0 : Nat))))) (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@Nat.instAddMonoid))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v16) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@True) (@lt_mul_iff_one_lt_left'._simp_4.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@Nat.instAddMonoid)) (@instLTNat) (@IsRightCancelAdd.addRightStrictMono_of_addRightMono.{0} (@Nat)
  (@AddZeroClass.toAdd.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@Nat.instAddMonoid)))
  (@IsCancelAdd.toIsRightCancelAdd.{0} (@Nat) (@AddZeroClass.toAdd.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@Nat.instAddMonoid))) (@IsOrderedCancelAddMonoid.toIsCancelAdd.{0} (@Nat) (@Nat.instAddCommMonoid)
  (@Nat.instPartialOrder) (@Nat.instIsOrderedCancelAddMonoid))) (@Nat.instPartialOrder)
  (@covariant_swap_add_of_covariant_add.{0} (@Nat) (fun (_v23 : (@Nat)) =>
(fun (_v24 : (@Nat)) =>
(@LE.le.{0} (@Nat) (@Preorder.toLE.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) _v23
  _v24))) (@Nat.instAddCommSemigroup) (@IsOrderedAddMonoid.toAddLeftMono.{0} (@Nat) (@Nat.instAddCommMonoid)
  (@Nat.instPartialOrder) (@Nat.instIsOrderedAddMonoid)))) (@contravariant_swap_add_of_contravariant_add.{0} (@Nat) (fun
  (_v23 : (@Nat)) =>
(fun (_v24 : (@Nat)) =>
(@LT.lt.{0} (@Nat) (@instLTNat) _v23 _v24))) (@Nat.instAddCommSemigroup) (@contravariant_lt_of_covariant_le.{0} (@Nat)
  (fun (_v23 : (@Nat)) =>
(fun (_v24 : (@Nat)) =>
(@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@AddCommMagma.toAdd.{0} (@Nat)
  (@AddCommSemigroup.toAddCommMagma.{0} (@Nat) (@Nat.instAddCommSemigroup)))) _v23 _v24))) (@Nat.instLinearOrder)
  (@IsOrderedAddMonoid.toAddLeftMono.{0} (@Nat) (@Nat.instAddCommMonoid) (@Nat.instPartialOrder)
  (@Nat.instIsOrderedAddMonoid)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v16) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Eq.trans.{(0 + 1)}
  (Sort 0) (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@AddZeroClass.toAdd.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v16) (@OfNat.ofNat.{0} (@Nat) (1 :
  Nat) (@instOfNatNat (1 : Nat))))) (@Or (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0}
  (@Nat) (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0}
  (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v16)) (@LT.lt.{0} (@Nat)
  (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 :
  Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat))))) (@True) (@one_lt_mul_iff._simp_4.{0} (@Nat) (@Nat.instAddCommMonoid) (@Nat.instPartialOrder)
  (@Nat.instCanonicallyOrderedAdd) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  _v16) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Eq.trans.{(0 + 1)} (Sort 0) (@Or (@LT.lt.{0}
  (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@AddZeroClass.toAdd.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))) _v1 _v16)) (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0}
  (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@One.toOfNat1.{0} (@Nat) (@Nat.instOne))))) (@Or (@Or (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat)
  (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0}
  (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat)
  (@Nat.instAddCommMonoid)))))) _v1) (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat)
  (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v16))
  (@True)) (@True) (@congr.{(0 + 1), (0 + 1)} (Sort 0) (Sort 0) (@Or (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat)
  (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0}
  (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat)
  (@Nat.instAddCommMonoid)))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@AddZeroClass.toAdd.{0}
  (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))) _v1
  _v16))) (@Or (@Or (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat)
  (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v1)
  (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v16)))
  (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))))
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@One.toOfNat1.{0} (@Nat) (@Nat.instOne)))) (@True) (@congrArg.{(0 + 1), (0 + 1)}
  (Sort 0) (∀ (_v23 : (Sort 0)),
(Sort 0)) (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@AddZeroClass.toAdd.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))) _v1 _v16))
  (@Or (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v1)
  (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v16)) (@Or)
  (@one_lt_mul_iff._simp_4.{0} (@Nat) (@Nat.instAddCommMonoid) (@Nat.instPartialOrder) (@Nat.instCanonicallyOrderedAdd)
  _v1 _v16)) (@zero_lt_one._simp_1.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))) (@Nat.instOne) (@Nat.instPartialOrder)
  (@instZeroLEOneClass.{0} (@Nat) (@Nat.instSemiring) (@Nat.instPartialOrder) (@Nat.instStarRing)
  (@Nat.instStarOrderedRing)) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))))
  (@or_true (@Or (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat)
  (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v1)
  (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v16))))))))
  (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v18) _v1 _v16 _v20)))
  (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.encodedRelationLanguage
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0) _v1 _v2) (@Bool.false)))))
  (@Exists.{(0 + 1)} (@Nat) (fun (_v23 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v24 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v23) (fun (_v25 : (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v23)) =>
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v24) (fun (_v26 : (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v24)) =>
(@Exists.{0} (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v23 _v24) _v1) (fun (_v27 :
  (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v23 _v24) _v1)) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.decodePair _v1 _v2) (@Option.some.{0} (@Prod.{0, 0} (@Sigma.{0, 0} (@Nat) (fun
  (_v28 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v28))) (@Sigma.{0, 0} (@Nat) (fun (_v28 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v28)))) (@Prod.mk.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v28 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v28))) (@Sigma.{0, 0} (@Nat) (fun (_v28 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v28))) (@Sigma.mk.{0, 0} (@Nat) (fun (_v28 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v28)) _v23 _v25) (@Sigma.mk.{0, 0} (@Nat) (fun (_v28 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v28)) _v24 _v26)))) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v1) _v2 (@Eq.rec.{(0 + 1), (0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v23 _v24) (fun (_v28 :
  (@Nat)) =>
(fun (_v29 : (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v23 _v24) _v28)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v28))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v23 _v24 _v25 _v26)
  _v1 _v27)) (@Exists.{(0 + 1)} (@Nat) (fun (_v28 : (@Nat)) =>
(@And (@Eq.{(0 + 1)} (@Nat) _v15 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp3.Complexity.Uniform.V1.FixedPairParser.clock _v1) _v28)) (@And (∀ (_v29 : (@Nat)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v18) _v1 _v16)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v18 _v1 _v16 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.FixedPairParser.clock _v1) _v29) _v20) (@TotalIngressClosure.config
  _v0 _v1 _v16 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v19 _v1 _v16 _v29 _v22)))) (@Exists.{0} (@LE.le.{0} (@Nat)
  (@instLENat) _v17 _v16) (fun (_v29 : (@LE.le.{0} (@Nat) (@instLENat) _v17 _v16)) =>
(@And (@Pnp3.Complexity.Uniform.V1.FixedPairParser.ConfigExtension (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  _v19) _v1 _v17 _v16 _v29 _v21 _v22) (@And (@IngressAllocation.Footprint _v19 _v1 _v17 _v2 _v28 (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 :
  Nat))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat)))))) (@And (@IngressAllocation.MoveRoom _v19 _v1 _v17 _v2 _v28) (@And (@IngressAllocation.Trace _v19 _v1 _v17 _v16
  _v29 _v2 _v28) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v18) _v1 _v16) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v18 _v1
  _v16 _v15 _v20) (@TotalIngressClosure.config _v0 _v1 _v16 (@IngressAllocation.extendConfig
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)) _v1 _v17 _v16 _v29
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v19 _v1 _v17 _v28 _v21)))) (@Or (@And (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v19)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v19) _v1 _v17 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v19 _v1
  _v17 _v28 _v21)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v19)) (@Eq.{(0 + 1)} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v23 _v24 _v25 _v26) (@Bool.false)))
  (@Exists.{(0 + 1)} (@Nat) (fun (_v30 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v31 : (@Nat)) =>
(@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v23 _v24) _v31) _v30) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v17)) (fun (_v32 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v23 _v24) _v31) _v30) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v17))) =>
(@And (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.tagMatches (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v23 _v24) (@Fin.append.{(0 + 1)} _v23 _v24 (@Bool) _v25 _v26))
  (@Bool.true)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Nat))
  (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros? (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v23 _v24) (@Fin.append.{(0 + 1)} _v23 _v24 (@Bool) _v25 _v26)) (@Option.some.{0}
  (@Nat) _v31)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Nat) (@Nat)))
  (@Pnp4.Frontier.ContractExpansion.contentHeader? (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v23 _v24) (@Fin.append.{(0 + 1)} _v23 _v24 (@Bool) _v25 _v26)) (@Option.some.{0} (@Prod.{0, 0} (@Nat)
  (@Nat)) (@Prod.mk.{0, 0} (@Nat) (@Nat) _v30 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v31) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))) (let _v33 :
  (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v23 _v24);
(let _v34 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v33 _v31) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))));
(let _v35 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v1);
(let _v36 : (@Nat) := (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0}
  (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v30);
(let _v37 : (@Nat) := (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v31)) _v36) _v33);
(let _v38 : (@Nat) := (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v33 _v37);
(let _v39 : (@Nat) := (@Cursor.Target.W _v0 _v30);
(let _v40 : (@Nat) := (@Cursor.Target.M _v0 _v30 _v31);
(let _v41 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v17)) := (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v1 _v17) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v33 _v31) _v30) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v32);
(let _v42 : (∀ (_v42 : (@Nat)),
(@Option.{0} (@Bool))) := (@Body.extend (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v23 _v24) _v17
  (@Body.installedTape (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v23 _v24) _v17 (@SmallIngress.prepared _v23
  _v24 _v17 _v25 _v26 _v31 _v30) _v34 _v30));
(let _v43 : (∀ (_v43 : (@Nat)),
(@Option.{0} (@Bool))) := (@Stream.Target.image _v42 _v33 _v31 _v30 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v31)) _v36 _v36 (@Bool.false));
(let _v44 : (∀ (_v44 : (@Nat)),
(@Option.{0} (@Bool))) := (@CappedWorkspace.Target.image (@SuffixCap.Target.image _v43 _v35 _v38) _v34 _v30 _v35 _v38);
(let _v45 : (∀ (_v45 : (@Nat)),
(@Option.{0} (@Bool))) := (@RuntimeBitLength.Target.fullImage _v44 _v34 _v30 _v35 _v38);
(let _v46 : (∀ (_v46 : (@Nat)),
(@Option.{0} (@Bool))) := (@AllArityBitLength.Target.seedImage _v45 _v35 _v38 _v30);
(let _v47 : (∀ (_v47 : (@Nat)),
(@Option.{0} (@Bool))) := (@CarryWindow.Target.image (@CappedWeight.Target.image _v46 _v34 _v30 _v35 _v38
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0}
  (@Nat) (@Nat.instMonoid))) _v30 _v0) _v0) _v39 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v35 _v38 _v30 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v30 _v0) _v0) (@Pnp4.Frontier.ContractExpansion.bitLength _v39)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) _v39);
(@And (@LT.lt.{0} (@Nat) (@instLTNat) _v30 (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.capacity _v23 _v24 _v31))
  (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v17) _v41) _v36) _v35) (@Or (@And (@LT.lt.{0} (@Nat) (@instLTNat)
  _v37 _v33) (@And (@LE.le.{0} (@Nat) (@instLENat) (@Pnp4.Frontier.ContractExpansion.bitLength _v30) _v38) (@And
  (@LE.le.{0} (@Nat) (@instLENat) _v39 _v38) (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter _v35 _v38
  _v30 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v17))
  (@And (∀ (_v48 : (@Nat)),
(∀ (_v49 : (@LE.le.{0} (@Nat) (@instLENat) _v40 _v48)),
(∀ (_v50 : (@LT.lt.{0} (@Nat) (@instLTNat) _v48 _v33)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v47 _v48) (@Option.some.{0} (@Bool) (@Fin.append.{(0 + 1)} _v23 _v24 (@Bool)
  _v25 _v26 (@Fin.mk (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v23 _v24) _v48
  _v50))))))) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v19)
  _v1 _v17) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v19 _v1 _v17 _v28 _v21) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v19) _v1 _v17 (@BodyIngress.body _v0 (@SerializedBody.entry
  (@SerializedBody.sourceMode (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v23 _v24)
  (@Fin.append.{(0 + 1)} _v23 _v24 (@Bool) _v25 _v26) _v40))) _v41 (fun (_v48 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v17))) =>
(@SerializedBody.prepared _v47 _v33 _v40 _v35 _v38 _v30 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) _v30 _v0) _v0) _v39 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v17) _v48))))))))))
  (@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v30) (fun
  (_v48 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v30)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v33 _v40) (@And (∀ (_v49 : (@Fin _v39)),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v23 _v24) (@Fin.append.{(0 + 1)} _v23 _v24 (@Bool) _v25 _v26) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v40 (@Fin.val _v39 _v49))) (@Bool.false))) (@And (@Eq.{(0
  + 1)} (@Option.{0} (@Pnp3.Models.Circuit _v30)) (@Pnp4.Frontier.TreeCircuitWitnessCodec.decode
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v30 (fun (_v49 : (@Fin
  (@Pnp4.Frontier.TreeCircuitWitnessCodec.witnessBits (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v30)))
  =>
(@Bool.false))) (@Option.some.{0} (@Pnp3.Models.Circuit _v30) (@Pnp3.Models.Circuit.input _v30 (@Fin.mk _v30
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v48)))) (@Or (@And (@Eq.{(0 + 1)} (@Nat) _v37 _v33)
  (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v19) _v1 _v17)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v19 _v1 _v17 _v28 _v21) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v19) _v1 _v17 (@BodyIngress.old _v0 (@CarryWindow.embed _v0
  (@CanonicalLeaf.result _v0 (@Bool.false)))) _v41 (@Function.update.{(0 + 1), (0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v17)) (fun (_v49 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1
  _v17))) =>
(@Option.{0} (@Bool))) (@instDecidableEqFin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v17)) (fun (_v49 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v17))) =>
(@_v43 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v17) _v49))) _v41 (@Option.some.{0} (@Bool)
  (@Bool.false)))))) (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v37 _v33) (@And (@Or (@LT.lt.{0} (@Nat) (@instLTNat) _v38
  (@Pnp4.Frontier.ContractExpansion.bitLength _v30)) (@And (@LE.le.{0} (@Nat) (@instLENat)
  (@Pnp4.Frontier.ContractExpansion.bitLength _v30) _v38) (@Exists.{(0 + 1)} (@Nat) (fun (_v49 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v50 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v51 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v52 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v53 : (@Nat)) =>
(@CappedWeight.Target.Cap _v0 _v30 _v38 _v49 _v50 _v51 _v52 _v53))))))))))))) (@Eq.{(0 + 1)}
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v19) _v1 _v17)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v19 _v1 _v17 _v28 _v21) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v19) _v1 _v17 (@BodyIngress.old _v0 (@CarryWindow.embed _v0
  (@CanonicalLeaf.result _v0 (@Bool.false)))) _v41 (@Function.update.{(0 + 1), (0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v17)) (fun (_v49 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1
  _v17))) =>
(@Option.{0} (@Bool))) (@instDecidableEqFin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v17)) (fun (_v49 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v17))) =>
(@Cursor.Target.image _v43 _v0 _v33 _v30 _v31 _v35 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v17) _v49)))
  _v41 (@Option.some.{0} (@Bool) (@Bool.false))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3 _v8 _v6) (@CertificateGuardClosure.config _v0 _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v5 _v1 _v3 _v15 _v7)))))))))))))))))))))))))))))))))))))))))) := by
  exact @CertificateGuardClosure.Audit.check_raw

-- Complete literal proposition for CertificateGuardClosure.Audit.check_raw; original proof reused.
theorem PartACanonical.Surface.m0190 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(let _v3 : (@Nat) := (@CertificateGuardClosure.allocation _v0 _v1);
(let _v4 : (@Pnp3.Complexity.Uniform.V1.UniformTM) := (@CertificateGuardClosure.machine _v0);
(let _v5 : (@Pnp3.Complexity.Uniform.V1.UniformTM) := (@TotalIngressClosure.machine _v0);
(let _v6 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v4 _v1 _v3 _v2);
(let _v7 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5) _v1 _v3) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v5 _v1 _v3 _v2);
(@Exists.{(0 + 1)} (@Nat) (fun (_v8 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v8 (@CertificateGuardClosure.deadline _v0 _v1)) (@And (∀ (_v9 : (@Nat)),
(∀ (_v10 : (@LE.le.{0} (@Nat) (@instLENat) _v9 _v8)),
(@LE.le.{0} (@Nat) (@instLENat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3 _v9 _v6))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))) (@HPow.hPow.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))))) (@And (∀ (_v9 : (@Nat)),
(∀ (_v10 : (@LE.le.{0} (@Nat) (@instLENat) _v9 _v8)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3
  _v9 _v6)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v4)))) (@And (∀ (_v9 : (@Nat)),
(∀ (_v10 : (@LT.lt.{0} (@Nat) (@instLTNat) _v9 _v8)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3 _v9 _v6)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v4))
  (@And (∀ (_v11 : (@Bool)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3
  _v9 _v6)) (@CertificateGuardClosure.old _v0 (@TotalIngressClosure.old _v0 (@BodyIngress.old _v0 (@CarryWindow.embed _v0
  (@CanonicalLeaf.result _v0 _v11))))))) (∀ (_v11 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3
  _v9 _v6)) (@CertificateGuardClosure.old _v0 (@TotalIngressClosure.old _v0 (@BodyIngress.body _v0 (@SerializedBody.entry
  _v11)))))))))) (@Or (@And (@Eq.{(0 + 1)} (@Option.{0} (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.decodePair _v1 _v2) (@Option.none.{0}
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))) (@And (@Eq.{(0 + 1)} (@Nat) _v8
  (@Pnp3.Complexity.Uniform.V1.FixedPairParser.clock _v1)) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3
  _v8 _v6) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v4) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3)
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
  (@covariant_swap_add_of_covariant_add.{0} (@Nat) (fun (_v9 : (@Nat)) =>
(fun (_v10 : (@Nat)) =>
(@LE.le.{0} (@Nat) (@Preorder.toLE.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) _v9 _v10)))
  (@Nat.instAddCommSemigroup) (@IsOrderedAddMonoid.toAddLeftMono.{0} (@Nat) (@Nat.instAddCommMonoid)
  (@Nat.instPartialOrder) (@Nat.instIsOrderedAddMonoid)))) (@contravariant_swap_add_of_contravariant_add.{0} (@Nat) (fun
  (_v9 : (@Nat)) =>
(fun (_v10 : (@Nat)) =>
(@LT.lt.{0} (@Nat) (@instLTNat) _v9 _v10))) (@Nat.instAddCommSemigroup) (@contravariant_lt_of_covariant_le.{0} (@Nat)
  (fun (_v9 : (@Nat)) =>
(fun (_v10 : (@Nat)) =>
(@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@AddCommMagma.toAdd.{0} (@Nat)
  (@AddCommSemigroup.toAddCommMagma.{0} (@Nat) (@Nat.instAddCommSemigroup)))) _v9 _v10))) (@Nat.instLinearOrder)
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
  (Sort 0) (∀ (_v9 : (Sort 0)),
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
  (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3 _v6))) (@Eq.{(0
  + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.encodedRelationLanguage
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0) _v1 _v2) (@Bool.false))))) (@Or
  (@Exists.{(0 + 1)} (@Nat) (fun (_v9 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v10 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v9) (fun (_v11 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v9))
  =>
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v10) (fun (_v12 : (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v10)) =>
(@Exists.{0} (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v9 _v10) _v1) (fun (_v13 :
  (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v9 _v10) _v1)) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.decodePair _v1 _v2) (@Option.some.{0} (@Prod.{0, 0} (@Sigma.{0, 0} (@Nat) (fun
  (_v14 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v14))) (@Sigma.{0, 0} (@Nat) (fun (_v14 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v14)))) (@Prod.mk.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v14 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v14))) (@Sigma.{0, 0} (@Nat) (fun (_v14 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v14))) (@Sigma.mk.{0, 0} (@Nat) (fun (_v14 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v14)) _v9 _v11) (@Sigma.mk.{0, 0} (@Nat) (fun (_v14 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v14)) _v10 _v12)))) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v1) _v2 (@Eq.rec.{(0 + 1), (0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v9 _v10) (fun (_v14 :
  (@Nat)) =>
(fun (_v15 : (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v9 _v10) _v14)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v14))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v9 _v10 _v11 _v12)
  _v1 _v13)) (@And (@Ne.{(0 + 1)} (@Nat) _v10 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v9 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@And (@LE.le.{0} (@Nat) (@instLENat)
  _v8 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp3.Complexity.Uniform.V1.FixedPairParser.clock _v1) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))))) (@And (@Eq.{(0 + 1)}
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3 _v8 _v6) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v4)
  (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@of_eq_true (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@AddZeroClass.toAdd.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@Nat.instAddMonoid)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v3)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))))) (@Eq.trans.{(0 + 1)} (Sort 0) (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@AddZeroClass.toAdd.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@Nat.instAddMonoid)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v3)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))))) (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat)
  (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@Nat.instAddMonoid))))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v3) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@True)
  (@lt_mul_iff_one_lt_left'._simp_4.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@Nat.instAddMonoid)) (@instLTNat)
  (@IsRightCancelAdd.addRightStrictMono_of_addRightMono.{0} (@Nat) (@AddZeroClass.toAdd.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@Nat.instAddMonoid))) (@IsCancelAdd.toIsRightCancelAdd.{0} (@Nat)
  (@AddZeroClass.toAdd.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@Nat.instAddMonoid)))
  (@IsOrderedCancelAddMonoid.toIsCancelAdd.{0} (@Nat) (@Nat.instAddCommMonoid) (@Nat.instPartialOrder)
  (@Nat.instIsOrderedCancelAddMonoid))) (@Nat.instPartialOrder) (@covariant_swap_add_of_covariant_add.{0} (@Nat) (fun
  (_v14 : (@Nat)) =>
(fun (_v15 : (@Nat)) =>
(@LE.le.{0} (@Nat) (@Preorder.toLE.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) _v14
  _v15))) (@Nat.instAddCommSemigroup) (@IsOrderedAddMonoid.toAddLeftMono.{0} (@Nat) (@Nat.instAddCommMonoid)
  (@Nat.instPartialOrder) (@Nat.instIsOrderedAddMonoid)))) (@contravariant_swap_add_of_contravariant_add.{0} (@Nat) (fun
  (_v14 : (@Nat)) =>
(fun (_v15 : (@Nat)) =>
(@LT.lt.{0} (@Nat) (@instLTNat) _v14 _v15))) (@Nat.instAddCommSemigroup) (@contravariant_lt_of_covariant_le.{0} (@Nat)
  (fun (_v14 : (@Nat)) =>
(fun (_v15 : (@Nat)) =>
(@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@AddCommMagma.toAdd.{0} (@Nat)
  (@AddCommSemigroup.toAddCommMagma.{0} (@Nat) (@Nat.instAddCommSemigroup)))) _v14 _v15))) (@Nat.instLinearOrder)
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
  (Sort 0) (∀ (_v14 : (Sort 0)),
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
  (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3 _v6))) (@Eq.{(0
  + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v9 _v10 _v11 _v12)
  (@Bool.false))))))))))))))))) (@Exists.{(0 + 1)} (@Nat) (fun (_v9 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v10 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v9) (fun (_v11 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v9))
  =>
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v10) (fun (_v12 : (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v10)) =>
(@Exists.{0} (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v9 _v10) _v1) (fun (_v13 :
  (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v9 _v10) _v1)) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.decodePair _v1 _v2) (@Option.some.{0} (@Prod.{0, 0} (@Sigma.{0, 0} (@Nat) (fun
  (_v14 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v14))) (@Sigma.{0, 0} (@Nat) (fun (_v14 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v14)))) (@Prod.mk.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v14 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v14))) (@Sigma.{0, 0} (@Nat) (fun (_v14 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v14))) (@Sigma.mk.{0, 0} (@Nat) (fun (_v14 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v14)) _v9 _v11) (@Sigma.mk.{0, 0} (@Nat) (fun (_v14 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v14)) _v10 _v12)))) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v1) _v2 (@Eq.rec.{(0 + 1), (0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v9 _v10) (fun (_v14 :
  (@Nat)) =>
(fun (_v15 : (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v9 _v10) _v14)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v14))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v9 _v10 _v11 _v12)
  _v1 _v13)) (@And (@Eq.{(0 + 1)} (@Nat) _v10 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v9 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Exists.{(0 + 1)} (@Nat) (fun (_v14
  : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v15 : (@Nat)) =>
(@And (@Eq.{(0 + 1)} (@Nat) _v8 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14
  _v15)) (@And (@LE.le.{0} (@Nat) (@instLENat) _v14 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.FixedPairParser.clock _v1) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) (@HPow.hPow.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))))) (@And (∀ (_v16 : (@Nat)),
(∀ (_v17 : (@LT.lt.{0} (@Nat) (@instLTNat) _v16 _v14)),
(@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4)
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3 _v16 _v6))) (@OfNat.ofNat.{0} (@Nat) (77 : Nat) (@instOfNatNat
  (77 : Nat)))))) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3
  _v14 _v6) (@CertificateGuardClosure.config _v0 _v1 _v3 _v7)) (@And (∀ (_v16 : (@Nat)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v14 _v16) _v6) (@CertificateGuardClosure.config _v0 _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  _v5 _v1 _v3 _v16 _v7)))) (@And (let _v16 : (@Nat) := (@TotalIngressClosure.allocation _v0 _v1);
(let _v17 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation _v1);
(let _v18 : (@Pnp3.Complexity.Uniform.V1.UniformTM) := (@TotalIngressClosure.machine _v0);
(let _v19 : (@Pnp3.Complexity.Uniform.V1.UniformTM) := (@BodyIngress.machine _v0);
(let _v20 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v18) _v1 _v16) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v18 _v1 _v16 _v2);
(let _v21 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v19) _v1 _v17) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v19 _v1 _v17 _v2);
(let _v22 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v19) _v1 _v16) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v19 _v1 _v16 _v2);
(@And (@LE.le.{0} (@Nat) (@instLENat) _v15 (@TotalIngressClosure.deadline _v0 _v1)) (@And (∀ (_v23 : (@Nat)),
(∀ (_v24 : (@LE.le.{0} (@Nat) (@instLENat) _v23 _v15)),
(@LE.le.{0} (@Nat) (@instLENat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v16)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v18) _v1 _v16
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v18 _v1 _v16 _v23 _v20))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))) (@HPow.hPow.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))))) (@And (∀ (_v23 : (@Nat)),
(∀ (_v24 : (@LE.le.{0} (@Nat) (@instLENat) _v23 _v15)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v18)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v18) _v1 _v16 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v18 _v1
  _v16 _v23 _v20)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v18)))) (@And (∀ (_v23 : (@Nat)),
(∀ (_v24 : (@LT.lt.{0} (@Nat) (@instLTNat) _v23 _v15)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v18))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v18) _v1 _v16
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v18 _v1 _v16 _v23 _v20)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject
  _v18)) (@And (∀ (_v25 : (@Bool)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v18)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v18) _v1 _v16 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v18 _v1
  _v16 _v23 _v20)) (@TotalIngressClosure.old _v0 (@BodyIngress.old _v0 (@CarryWindow.embed _v0 (@CanonicalLeaf.result _v0
  _v25)))))) (∀ (_v25 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v18)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v18) _v1 _v16 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v18 _v1
  _v16 _v23 _v20)) (@TotalIngressClosure.old _v0 (@BodyIngress.body _v0 (@SerializedBody.entry _v25))))))))) (@Or (@And
  (@Eq.{(0 + 1)} (@Option.{0} (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.decodePair _v1 _v2) (@Option.none.{0}
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))) (@And (@Eq.{(0 + 1)} (@Nat) _v15
  (@Pnp3.Complexity.Uniform.V1.FixedPairParser.clock _v1)) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v18) _v1 _v16) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v18 _v1
  _v16 _v15 _v20) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v18) _v1 _v16
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v18) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v16)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@of_eq_true (@LT.lt.{0} (@Nat) (@instLTNat)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@AddZeroClass.toAdd.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@Nat.instAddMonoid)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v16) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat)
  (0 : Nat) (@instOfNatNat (0 : Nat))))) (@Eq.trans.{(0 + 1)} (Sort 0) (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@AddZeroClass.toAdd.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@Nat.instAddMonoid)))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v16) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat)
  (0 : Nat) (@instOfNatNat (0 : Nat))))) (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@Nat.instAddMonoid))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v16) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@True) (@lt_mul_iff_one_lt_left'._simp_4.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@Nat.instAddMonoid)) (@instLTNat) (@IsRightCancelAdd.addRightStrictMono_of_addRightMono.{0} (@Nat)
  (@AddZeroClass.toAdd.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@Nat.instAddMonoid)))
  (@IsCancelAdd.toIsRightCancelAdd.{0} (@Nat) (@AddZeroClass.toAdd.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@Nat.instAddMonoid))) (@IsOrderedCancelAddMonoid.toIsCancelAdd.{0} (@Nat) (@Nat.instAddCommMonoid)
  (@Nat.instPartialOrder) (@Nat.instIsOrderedCancelAddMonoid))) (@Nat.instPartialOrder)
  (@covariant_swap_add_of_covariant_add.{0} (@Nat) (fun (_v23 : (@Nat)) =>
(fun (_v24 : (@Nat)) =>
(@LE.le.{0} (@Nat) (@Preorder.toLE.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) _v23
  _v24))) (@Nat.instAddCommSemigroup) (@IsOrderedAddMonoid.toAddLeftMono.{0} (@Nat) (@Nat.instAddCommMonoid)
  (@Nat.instPartialOrder) (@Nat.instIsOrderedAddMonoid)))) (@contravariant_swap_add_of_contravariant_add.{0} (@Nat) (fun
  (_v23 : (@Nat)) =>
(fun (_v24 : (@Nat)) =>
(@LT.lt.{0} (@Nat) (@instLTNat) _v23 _v24))) (@Nat.instAddCommSemigroup) (@contravariant_lt_of_covariant_le.{0} (@Nat)
  (fun (_v23 : (@Nat)) =>
(fun (_v24 : (@Nat)) =>
(@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@AddCommMagma.toAdd.{0} (@Nat)
  (@AddCommSemigroup.toAddCommMagma.{0} (@Nat) (@Nat.instAddCommSemigroup)))) _v23 _v24))) (@Nat.instLinearOrder)
  (@IsOrderedAddMonoid.toAddLeftMono.{0} (@Nat) (@Nat.instAddCommMonoid) (@Nat.instPartialOrder)
  (@Nat.instIsOrderedAddMonoid)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v16) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Eq.trans.{(0 + 1)}
  (Sort 0) (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@AddZeroClass.toAdd.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v16) (@OfNat.ofNat.{0} (@Nat) (1 :
  Nat) (@instOfNatNat (1 : Nat))))) (@Or (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0}
  (@Nat) (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0}
  (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v16)) (@LT.lt.{0} (@Nat)
  (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 :
  Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat))))) (@True) (@one_lt_mul_iff._simp_4.{0} (@Nat) (@Nat.instAddCommMonoid) (@Nat.instPartialOrder)
  (@Nat.instCanonicallyOrderedAdd) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  _v16) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Eq.trans.{(0 + 1)} (Sort 0) (@Or (@LT.lt.{0}
  (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@AddZeroClass.toAdd.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))) _v1 _v16)) (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0}
  (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@One.toOfNat1.{0} (@Nat) (@Nat.instOne))))) (@Or (@Or (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat)
  (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0}
  (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat)
  (@Nat.instAddCommMonoid)))))) _v1) (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat)
  (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v16))
  (@True)) (@True) (@congr.{(0 + 1), (0 + 1)} (Sort 0) (Sort 0) (@Or (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat)
  (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0}
  (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat)
  (@Nat.instAddCommMonoid)))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@AddZeroClass.toAdd.{0}
  (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))) _v1
  _v16))) (@Or (@Or (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat)
  (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v1)
  (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v16)))
  (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))))
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@One.toOfNat1.{0} (@Nat) (@Nat.instOne)))) (@True) (@congrArg.{(0 + 1), (0 + 1)}
  (Sort 0) (∀ (_v23 : (Sort 0)),
(Sort 0)) (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@AddZeroClass.toAdd.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid))))) _v1 _v16))
  (@Or (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v1)
  (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v16)) (@Or)
  (@one_lt_mul_iff._simp_4.{0} (@Nat) (@Nat.instAddCommMonoid) (@Nat.instPartialOrder) (@Nat.instCanonicallyOrderedAdd)
  _v1 _v16)) (@zero_lt_one._simp_1.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat) (@AddMonoid.toAddZeroClass.{0} (@Nat)
  (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))) (@Nat.instOne) (@Nat.instPartialOrder)
  (@instZeroLEOneClass.{0} (@Nat) (@Nat.instSemiring) (@Nat.instPartialOrder) (@Nat.instStarRing)
  (@Nat.instStarOrderedRing)) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))))
  (@or_true (@Or (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat)
  (@Nat.instPartialOrder))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v1)
  (@LT.lt.{0} (@Nat) (@Preorder.toLT.{0} (@Nat) (@PartialOrder.toPreorder.{0} (@Nat) (@Nat.instPartialOrder)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@Zero.toOfNat0.{0} (@Nat) (@AddZeroClass.toZero.{0} (@Nat)
  (@AddMonoid.toAddZeroClass.{0} (@Nat) (@AddCommMonoid.toAddMonoid.{0} (@Nat) (@Nat.instAddCommMonoid)))))) _v16))))))))
  (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v18) _v1 _v16 _v20)))
  (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.encodedRelationLanguage
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0) _v1 _v2) (@Bool.false)))))
  (@Exists.{(0 + 1)} (@Nat) (fun (_v23 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v24 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v23) (fun (_v25 : (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v23)) =>
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v24) (fun (_v26 : (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v24)) =>
(@Exists.{0} (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v23 _v24) _v1) (fun (_v27 :
  (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v23 _v24) _v1)) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.decodePair _v1 _v2) (@Option.some.{0} (@Prod.{0, 0} (@Sigma.{0, 0} (@Nat) (fun
  (_v28 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v28))) (@Sigma.{0, 0} (@Nat) (fun (_v28 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v28)))) (@Prod.mk.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v28 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v28))) (@Sigma.{0, 0} (@Nat) (fun (_v28 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v28))) (@Sigma.mk.{0, 0} (@Nat) (fun (_v28 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v28)) _v23 _v25) (@Sigma.mk.{0, 0} (@Nat) (fun (_v28 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v28)) _v24 _v26)))) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v1) _v2 (@Eq.rec.{(0 + 1), (0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v23 _v24) (fun (_v28 :
  (@Nat)) =>
(fun (_v29 : (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v23 _v24) _v28)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v28))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v23 _v24 _v25 _v26)
  _v1 _v27)) (@Exists.{(0 + 1)} (@Nat) (fun (_v28 : (@Nat)) =>
(@And (@Eq.{(0 + 1)} (@Nat) _v15 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp3.Complexity.Uniform.V1.FixedPairParser.clock _v1) _v28)) (@And (∀ (_v29 : (@Nat)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v18) _v1 _v16)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v18 _v1 _v16 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.FixedPairParser.clock _v1) _v29) _v20) (@TotalIngressClosure.config
  _v0 _v1 _v16 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v19 _v1 _v16 _v29 _v22)))) (@Exists.{0} (@LE.le.{0} (@Nat)
  (@instLENat) _v17 _v16) (fun (_v29 : (@LE.le.{0} (@Nat) (@instLENat) _v17 _v16)) =>
(@And (@Pnp3.Complexity.Uniform.V1.FixedPairParser.ConfigExtension (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  _v19) _v1 _v17 _v16 _v29 _v21 _v22) (@And (∀ (_v30 : (@Nat)),
(∀ (_v31 : (@LE.le.{0} (@Nat) (@instLENat) _v30 _v28)),
(@LE.le.{0} (@Nat) (@instLENat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v17)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v19) _v1 _v17
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v19 _v1 _v17 _v30 (@Pnp3.Complexity.Uniform.V1.initialConfig _v19 _v1 _v17
  _v2)))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (12 :
  Nat) (@instOfNatNat (12 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat)))))))) (@And (∀ (_v30 : (@Nat)),
(∀ (_v31 : (@LT.lt.{0} (@Nat) (@instLTNat) _v30 _v28)),
(let _v32 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v19) _v1 _v17) :=
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v19 _v1 _v17 _v30 (@Pnp3.Complexity.Uniform.V1.initialConfig _v19 _v1 _v17
  _v2));
(∀ (_v33 : (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Move) (@Prod.snd.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move) (@Prod.snd.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v19))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step _v19
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v19) _v1 _v17 _v32)
  (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v19) _v1 _v17 _v32
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v19) _v1 _v17 _v32)))))
  (@Pnp3.Complexity.Uniform.V1.Move.right))),
(@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v17) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v19) _v1 _v17 _v32)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v17)))))) (@And (∀ (_v30 : (@Nat)),
(∀ (_v31 : (@LE.le.{0} (@Nat) (@instLENat) _v30 _v28)),
(@Pnp3.Complexity.Uniform.V1.FixedPairParser.ConfigExtension (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v19) _v1
  _v17 _v16 _v29 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v19 _v1 _v17 _v30 (@Pnp3.Complexity.Uniform.V1.initialConfig
  _v19 _v1 _v17 _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v19 _v1 _v16 _v30
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v19 _v1 _v16 _v2))))) (@And (@Eq.{(0 + 1)}
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v18) _v1 _v16)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v18 _v1 _v16 _v15 _v20) (@TotalIngressClosure.config _v0 _v1 _v16
  (@IngressAllocation.extendConfig (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)) _v1 _v17
  _v16 _v29 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v19 _v1 _v17 _v28 _v21)))) (@Or (@And (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v19)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v19) _v1 _v17 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v19 _v1
  _v17 _v28 _v21)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v19)) (@Eq.{(0 + 1)} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v23 _v24 _v25 _v26) (@Bool.false)))
  (@Exists.{(0 + 1)} (@Nat) (fun (_v30 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v31 : (@Nat)) =>
(@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v23 _v24) _v31) _v30) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v17)) (fun (_v32 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v23 _v24) _v31) _v30) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v17))) =>
(@And (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.tagMatches (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v23 _v24) (@Fin.append.{(0 + 1)} _v23 _v24 (@Bool) _v25 _v26))
  (@Bool.true)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Nat))
  (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros? (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v23 _v24) (@Fin.append.{(0 + 1)} _v23 _v24 (@Bool) _v25 _v26)) (@Option.some.{0}
  (@Nat) _v31)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Nat) (@Nat)))
  (@Pnp4.Frontier.ContractExpansion.contentHeader? (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v23 _v24) (@Fin.append.{(0 + 1)} _v23 _v24 (@Bool) _v25 _v26)) (@Option.some.{0} (@Prod.{0, 0} (@Nat)
  (@Nat)) (@Prod.mk.{0, 0} (@Nat) (@Nat) _v30 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v31) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))) (let _v33 :
  (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v23 _v24);
(let _v34 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v33 _v31) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))));
(let _v35 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v1);
(let _v36 : (@Nat) := (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0}
  (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v30);
(let _v37 : (@Nat) := (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v31)) _v36) _v33);
(let _v38 : (@Nat) := (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v33 _v37);
(let _v39 : (@Nat) := (@Cursor.Target.W _v0 _v30);
(let _v40 : (@Nat) := (@Cursor.Target.M _v0 _v30 _v31);
(let _v41 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v17)) := (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v1 _v17) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v33 _v31) _v30) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v32);
(let _v42 : (∀ (_v42 : (@Nat)),
(@Option.{0} (@Bool))) := (@Body.extend (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v23 _v24) _v17
  (@Body.installedTape (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v23 _v24) _v17 (@SmallIngress.prepared _v23
  _v24 _v17 _v25 _v26 _v31 _v30) _v34 _v30));
(let _v43 : (∀ (_v43 : (@Nat)),
(@Option.{0} (@Bool))) := (@Stream.Target.image _v42 _v33 _v31 _v30 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v31)) _v36 _v36 (@Bool.false));
(let _v44 : (∀ (_v44 : (@Nat)),
(@Option.{0} (@Bool))) := (@CappedWorkspace.Target.image (@SuffixCap.Target.image _v43 _v35 _v38) _v34 _v30 _v35 _v38);
(let _v45 : (∀ (_v45 : (@Nat)),
(@Option.{0} (@Bool))) := (@RuntimeBitLength.Target.fullImage _v44 _v34 _v30 _v35 _v38);
(let _v46 : (∀ (_v46 : (@Nat)),
(@Option.{0} (@Bool))) := (@AllArityBitLength.Target.seedImage _v45 _v35 _v38 _v30);
(let _v47 : (∀ (_v47 : (@Nat)),
(@Option.{0} (@Bool))) := (@CarryWindow.Target.image (@CappedWeight.Target.image _v46 _v34 _v30 _v35 _v38
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0}
  (@Nat) (@Nat.instMonoid))) _v30 _v0) _v0) _v39 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v35 _v38 _v30 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v30 _v0) _v0) (@Pnp4.Frontier.ContractExpansion.bitLength _v39)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) _v39);
(@And (@LT.lt.{0} (@Nat) (@instLTNat) _v30 (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.capacity _v23 _v24 _v31))
  (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v17) _v41) _v36) _v35) (@Or (@And (@LT.lt.{0} (@Nat) (@instLTNat)
  _v37 _v33) (@And (@LE.le.{0} (@Nat) (@instLENat) (@Pnp4.Frontier.ContractExpansion.bitLength _v30) _v38) (@And
  (@LE.le.{0} (@Nat) (@instLENat) _v39 _v38) (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter _v35 _v38
  _v30 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v17))
  (@And (∀ (_v48 : (@Nat)),
(∀ (_v49 : (@LE.le.{0} (@Nat) (@instLENat) _v40 _v48)),
(∀ (_v50 : (@LT.lt.{0} (@Nat) (@instLTNat) _v48 _v33)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v47 _v48) (@Option.some.{0} (@Bool) (@Fin.append.{(0 + 1)} _v23 _v24 (@Bool)
  _v25 _v26 (@Fin.mk (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v23 _v24) _v48
  _v50))))))) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v19)
  _v1 _v17) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v19 _v1 _v17 _v28 _v21) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v19) _v1 _v17 (@BodyIngress.body _v0 (@SerializedBody.entry
  (@SerializedBody.sourceMode (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v23 _v24)
  (@Fin.append.{(0 + 1)} _v23 _v24 (@Bool) _v25 _v26) _v40))) _v41 (fun (_v48 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v17))) =>
(@SerializedBody.prepared _v47 _v33 _v40 _v35 _v38 _v30 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) _v30 _v0) _v0) _v39 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v17) _v48))))))))))
  (@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v30) (fun
  (_v48 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v30)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v33 _v40) (@And (∀ (_v49 : (@Fin _v39)),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v23 _v24) (@Fin.append.{(0 + 1)} _v23 _v24 (@Bool) _v25 _v26) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v40 (@Fin.val _v39 _v49))) (@Bool.false))) (@And (@Eq.{(0
  + 1)} (@Option.{0} (@Pnp3.Models.Circuit _v30)) (@Pnp4.Frontier.TreeCircuitWitnessCodec.decode
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v30 (fun (_v49 : (@Fin
  (@Pnp4.Frontier.TreeCircuitWitnessCodec.witnessBits (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v30)))
  =>
(@Bool.false))) (@Option.some.{0} (@Pnp3.Models.Circuit _v30) (@Pnp3.Models.Circuit.input _v30 (@Fin.mk _v30
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v48)))) (@Or (@And (@Eq.{(0 + 1)} (@Nat) _v37 _v33)
  (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v19) _v1 _v17)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v19 _v1 _v17 _v28 _v21) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v19) _v1 _v17 (@BodyIngress.old _v0 (@CarryWindow.embed _v0
  (@CanonicalLeaf.result _v0 (@Bool.false)))) _v41 (@Function.update.{(0 + 1), (0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v17)) (fun (_v49 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1
  _v17))) =>
(@Option.{0} (@Bool))) (@instDecidableEqFin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v17)) (fun (_v49 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v17))) =>
(@_v43 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v17) _v49))) _v41 (@Option.some.{0} (@Bool)
  (@Bool.false)))))) (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v37 _v33) (@And (@Or (@LT.lt.{0} (@Nat) (@instLTNat) _v38
  (@Pnp4.Frontier.ContractExpansion.bitLength _v30)) (@And (@LE.le.{0} (@Nat) (@instLENat)
  (@Pnp4.Frontier.ContractExpansion.bitLength _v30) _v38) (@Exists.{(0 + 1)} (@Nat) (fun (_v49 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v50 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v51 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v52 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v53 : (@Nat)) =>
(@Or (@Exists.{(0 + 1)} (@Nat) (fun (_v54 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v55 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v56 : (@Nat)) =>
(@And (@LT.lt.{0} (@Nat) (@instLTNat) _v54 _v0) (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v55 (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v30 _v54)) (@And
  (@LT.lt.{0} (@Nat) (@instLTNat) _v56 _v30) (@And (@Eq.{(0 + 1)} (@Nat) _v38 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  _v55 _v30) _v56)) (@And (@Eq.{(0 + 1)} (@Nat) _v49 (@Pnp4.Frontier.ContractExpansion.bitLength _v30)) (@And (@Eq.{(0 +
  1)} (@Nat) _v50 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HSub.hSub.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0}
  (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v30 _v54) _v55) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@And (@Eq.{(0 + 1)} (@Nat) _v51 _v38) (@And (@Eq.{(0 + 1)} (@Nat) _v52 (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Eq.{(0 + 1)} (@Nat) _v53 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v56 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))))))))))))))))
  (@Or (@Exists.{(0 + 1)} (@Nat) (fun (_v54 : (@Nat)) =>
(@And (@LT.lt.{0} (@Nat) (@instLTNat) _v54 _v0) (@And (@Eq.{(0 + 1)} (@Nat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v30 _v0) _v54) _v38) (@And (@Eq.{(0 + 1)} (@Nat) _v49
  (@Pnp4.Frontier.ContractExpansion.bitLength _v30)) (@And (@Eq.{(0 + 1)} (@Nat) _v50 _v38) (@And (@Eq.{(0 + 1)} (@Nat)
  _v51 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@And (@Eq.{(0 + 1)} (@Nat) _v52 (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Eq.{(0 + 1)} (@Nat) _v53 (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))))))))))) (@Or (@Exists.{(0 + 1)} (@Nat) (fun (_v54 : (@Nat)) =>
(@And (@LT.lt.{0} (@Nat) (@instLTNat) _v54 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@And (@Eq.{(0
  + 1)} (@Nat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp4.Frontier.ContractExpansion.bitLength _v30) _v54) _v38) (@And (@Eq.{(0 + 1)} (@Nat) _v49 _v38) (@And (@Eq.{(0 +
  1)} (@Nat) _v50 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v30 _v0) _v0))
  (@And (@Eq.{(0 + 1)} (@Nat) _v51 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@And (@Eq.{(0 + 1)}
  (@Nat) _v52 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Eq.{(0 + 1)} (@Nat) _v53 (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))))))))))) (@Exists.{(0 + 1)} (@Nat) (fun (_v54 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v55 : (@Nat)) =>
(@And (@LT.lt.{0} (@Nat) (@instLTNat) _v54 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@Pnp4.Frontier.ContractExpansion.bitLength _v30) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v55 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) _v30 _v0) _v0)) (@And (@Eq.{(0 + 1)} (@Nat) _v38 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  _v54 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v30 _v0) _v0)) _v55)) (@And
  (@Eq.{(0 + 1)} (@Nat) _v49 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat))
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp4.Frontier.ContractExpansion.bitLength _v30) (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))) _v54) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@And
  (@Eq.{(0 + 1)} (@Nat) _v50 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat))
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v30 _v0) _v0) _v55) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat))))) (@And (@Eq.{(0 + 1)} (@Nat) _v51 _v38) (@And (@Eq.{(0 + 1)} (@Nat) _v52 _v55) (@Eq.{(0 + 1)} (@Nat) _v53
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))))))))))))))))))))))))))))) (@Eq.{(0 + 1)}
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v19) _v1 _v17)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v19 _v1 _v17 _v28 _v21) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v19) _v1 _v17 (@BodyIngress.old _v0 (@CarryWindow.embed _v0
  (@CanonicalLeaf.result _v0 (@Bool.false)))) _v41 (@Function.update.{(0 + 1), (0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v17)) (fun (_v49 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1
  _v17))) =>
(@Option.{0} (@Bool))) (@instDecidableEqFin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v17)) (fun (_v49 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v17))) =>
(@Cursor.Target.image _v43 _v0 _v33 _v30 _v31 _v35 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v17) _v49)))
  _v41 (@Option.some.{0} (@Bool) (@Bool.false))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3 _v8 _v6) (@CertificateGuardClosure.config _v0 _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v5 _v1 _v3 _v15 _v7)))))))))))))))))))))))))))))))))))))))))) := by
  exact @CertificateGuardClosure.Audit.check_raw

-- Independent literal expected type for CertificateGuardClosure.Audit.check_threshold_equation.
noncomputable def PartACanonical.Types.p0298 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.WitnessRelation)
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0)
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.contentWitnessRelation (@Pnp4.Frontier.ContractExpansion.thresholdPoly
  _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))))) := by
  exact @CertificateGuardClosure.Audit.check_threshold_equation

-- Complete literal proposition for CertificateGuardClosure.Audit.check_threshold_equation; original proof reused.
theorem PartACanonical.Surface.m0191 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.WitnessRelation)
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0)
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.contentWitnessRelation (@Pnp4.Frontier.ContractExpansion.thresholdPoly
  _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))))) := by
  exact @CertificateGuardClosure.Audit.check_threshold_equation

-- Independent literal expected type for CertificateGuardClosure.Target.Frontier.
noncomputable def PartACanonical.Types.p0299 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v3 : (@Nat)),
(Sort 0))))) := by
  exact @CertificateGuardClosure.Target.Frontier

-- Independent literal expected type for CertificateGuardClosure.Target.Raw.
noncomputable def PartACanonical.Types.p0300 :
(∀ (_v0 : (@Nat)),
(Sort 0)) := by
  exact @CertificateGuardClosure.Target.Raw

-- Independent literal expected type for CertificateGuardClosure.allocation.
noncomputable def PartACanonical.Types.p0301 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(@Nat))) := by
  exact @CertificateGuardClosure.allocation

-- Independent literal expected type for CertificateGuardClosure.component_rows.
noncomputable def PartACanonical.Types.p0302 :
(∀ (_v0 : (@Nat)),
(@And (@Function.Injective.{(0 + 1), (0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@TotalIngressClosure.machine _v0))) (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@CertificateGuardClosure.machine _v0))) (@CertificateGuardClosure.old _v0)) (@And (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CertificateGuardClosure.machine _v0))) (@CertificateGuardClosure.old
  _v0 (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@TotalIngressClosure.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@CertificateGuardClosure.machine _v0))) (@And (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CertificateGuardClosure.machine _v0))) (@CertificateGuardClosure.old
  _v0 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@TotalIngressClosure.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@CertificateGuardClosure.machine _v0))) (∀ (_v1 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@TotalIngressClosure.machine _v0)))),
(∀ (_v2 : (@Option.{0} (@Bool))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CertificateGuardClosure.machine
  _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@CertificateGuardClosure.machine _v0) (@CertificateGuardClosure.old _v0
  _v1) _v2) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CertificateGuardClosure.machine
  _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@CertificateGuardClosure.old _v0
  (@Prod.fst.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@TotalIngressClosure.machine _v0)))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step
  (@TotalIngressClosure.machine _v0) _v1 _v2))) (@Prod.snd.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@TotalIngressClosure.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@TotalIngressClosure.machine _v0) _v1 _v2)))))))))) := by
  exact @CertificateGuardClosure.component_rows

-- Complete literal proposition for CertificateGuardClosure.component_rows; original proof reused.
theorem PartACanonical.Surface.m0192 :
(∀ (_v0 : (@Nat)),
(@And (@Function.Injective.{(0 + 1), (0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@TotalIngressClosure.machine _v0))) (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@CertificateGuardClosure.machine _v0))) (@CertificateGuardClosure.old _v0)) (@And (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CertificateGuardClosure.machine _v0))) (@CertificateGuardClosure.old
  _v0 (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@TotalIngressClosure.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@CertificateGuardClosure.machine _v0))) (@And (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CertificateGuardClosure.machine _v0))) (@CertificateGuardClosure.old
  _v0 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@TotalIngressClosure.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@CertificateGuardClosure.machine _v0))) (∀ (_v1 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@TotalIngressClosure.machine _v0)))),
(∀ (_v2 : (@Option.{0} (@Bool))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CertificateGuardClosure.machine
  _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@CertificateGuardClosure.machine _v0) (@CertificateGuardClosure.old _v0
  _v1) _v2) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CertificateGuardClosure.machine
  _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@CertificateGuardClosure.old _v0
  (@Prod.fst.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@TotalIngressClosure.machine _v0)))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step
  (@TotalIngressClosure.machine _v0) _v1 _v2))) (@Prod.snd.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@TotalIngressClosure.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@TotalIngressClosure.machine _v0) _v1 _v2)))))))))) := by
  exact @CertificateGuardClosure.component_rows

-- Independent literal expected type for CertificateGuardClosure.config.
noncomputable def PartACanonical.Types.p0303 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@TotalIngressClosure.machine _v0)) _v1 _v2)),
(@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CertificateGuardClosure.machine
  _v0)) _v1 _v2))))) := by
  exact @CertificateGuardClosure.config

-- Independent literal expected type for CertificateGuardClosure.deadline.
noncomputable def PartACanonical.Types.p0304 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(@Nat))) := by
  exact @CertificateGuardClosure.deadline

-- Independent literal expected type for CertificateGuardClosure.exists_canonical.
noncomputable def PartACanonical.Types.p0305 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(@Iff (@Exists.{(0 + 1)} (@Nat) (fun (_v3 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v3) (fun (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v3))
  =>
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v1 _v3 _v2
  _v4) (@Bool.true)))))) (@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (fun
  (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) =>
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v1
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))) _v2 _v3) (@Bool.true)))))))) := by
  exact @CertificateGuardClosure.exists_canonical

-- Complete literal proposition for CertificateGuardClosure.exists_canonical; original proof reused.
theorem PartACanonical.Surface.m0193 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(@Iff (@Exists.{(0 + 1)} (@Nat) (fun (_v3 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v3) (fun (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v3))
  =>
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v1 _v3 _v2
  _v4) (@Bool.true)))))) (@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (fun
  (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) =>
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v1
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))) _v2 _v3) (@Bool.true)))))))) := by
  exact @CertificateGuardClosure.exists_canonical

-- Independent literal expected type for CertificateGuardClosure.exists_canonical_mirror.
noncomputable def PartACanonical.Types.p0306 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(@Iff (@Exists.{(0 + 1)} (@Nat) (fun (_v3 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v3) (fun (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v3))
  =>
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v1 _v3 _v2
  _v4) (@Bool.true)))))) (@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (fun
  (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) =>
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v1
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))) _v2 _v3) (@Bool.true)))))))) := by
  exact @CertificateGuardClosure.exists_canonical_mirror

-- Complete literal proposition for CertificateGuardClosure.exists_canonical_mirror; original proof reused.
theorem PartACanonical.Surface.m0194 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(@Iff (@Exists.{(0 + 1)} (@Nat) (fun (_v3 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v3) (fun (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v3))
  =>
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v1 _v3 _v2
  _v4) (@Bool.true)))))) (@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (fun
  (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) =>
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v1
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))) _v2 _v3) (@Bool.true)))))))) := by
  exact @CertificateGuardClosure.exists_canonical_mirror

-- Independent literal expected type for CertificateGuardClosure.guard.
noncomputable def PartACanonical.Types.p0307 :
(@Pnp3.Complexity.Uniform.V1.UniformTM) := by
  exact @CertificateGuardClosure.guard

-- Independent literal expected type for CertificateGuardClosure.machine.
noncomputable def PartACanonical.Types.p0309 :
(∀ (_v0 : (@Nat)),
(@Pnp3.Complexity.Uniform.V1.UniformTM)) := by
  exact @CertificateGuardClosure.machine

-- Independent literal expected type for CertificateGuardClosure.old.
noncomputable def PartACanonical.Types.p0310 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@TotalIngressClosure.machine _v0)))),
(@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CertificateGuardClosure.machine _v0))))) := by
  exact @CertificateGuardClosure.old

-- Independent literal expected type for CertificateGuardClosure.raw.
noncomputable def PartACanonical.Types.p0311 :
(∀ (_v0 : (@Nat)),
(@CertificateGuardClosure.Target.Raw _v0)) := by
  exact @CertificateGuardClosure.raw

-- Complete literal proposition for CertificateGuardClosure.raw; original proof reused.
theorem PartACanonical.Surface.m0196 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(let _v3 : (@Nat) := (@CertificateGuardClosure.allocation _v0 _v1);
(let _v4 : (@Pnp3.Complexity.Uniform.V1.UniformTM) := (@CertificateGuardClosure.machine _v0);
(let _v5 : (@Pnp3.Complexity.Uniform.V1.UniformTM) := (@TotalIngressClosure.machine _v0);
(let _v6 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v4 _v1 _v3 _v2);
(let _v7 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v5) _v1 _v3) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v5 _v1 _v3 _v2);
(@Exists.{(0 + 1)} (@Nat) (fun (_v8 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v8 (@CertificateGuardClosure.deadline _v0 _v1)) (@And (∀ (_v9 : (@Nat)),
(∀ (_v10 : (@LE.le.{0} (@Nat) (@instLENat) _v9 _v8)),
(@LE.le.{0} (@Nat) (@instLENat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3 _v9 _v6))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))) (@HPow.hPow.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))))) (@And (∀ (_v9 : (@Nat)),
(∀ (_v10 : (@LE.le.{0} (@Nat) (@instLENat) _v9 _v8)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3
  _v9 _v6)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v4)))) (@And (∀ (_v9 : (@Nat)),
(∀ (_v10 : (@LT.lt.{0} (@Nat) (@instLTNat) _v9 _v8)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3 _v9 _v6)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v4))
  (@And (∀ (_v11 : (@Bool)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3
  _v9 _v6)) (@CertificateGuardClosure.old _v0 (@TotalIngressClosure.old _v0 (@BodyIngress.old _v0 (@CarryWindow.embed _v0
  (@CanonicalLeaf.result _v0 _v11))))))) (∀ (_v11 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3
  _v9 _v6)) (@CertificateGuardClosure.old _v0 (@TotalIngressClosure.old _v0 (@BodyIngress.body _v0 (@SerializedBody.entry
  _v11)))))))))) (@Or (@And (@Eq.{(0 + 1)} (@Option.{0} (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.decodePair _v1 _v2) (@Option.none.{0}
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))) (@And (@Eq.{(0 + 1)} (@Nat) _v8
  (@Pnp3.Complexity.Uniform.V1.FixedPairParser.clock _v1)) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3
  _v8 _v6) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v4) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@CertificateGuardClosure.Target.Raw._proof_1 _v0 _v1))
  (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3 _v6))) (@Eq.{(0
  + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.encodedRelationLanguage
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0) _v1 _v2) (@Bool.false))))) (@Or
  (@Exists.{(0 + 1)} (@Nat) (fun (_v9 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v10 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v9) (fun (_v11 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v9))
  =>
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v10) (fun (_v12 : (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v10)) =>
(@Exists.{0} (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v9 _v10) _v1) (fun (_v13 :
  (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v9 _v10) _v1)) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.decodePair _v1 _v2) (@Option.some.{0} (@Prod.{0, 0} (@Sigma.{0, 0} (@Nat) (fun
  (_v14 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v14))) (@Sigma.{0, 0} (@Nat) (fun (_v14 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v14)))) (@Prod.mk.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v14 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v14))) (@Sigma.{0, 0} (@Nat) (fun (_v14 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v14))) (@Sigma.mk.{0, 0} (@Nat) (fun (_v14 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v14)) _v9 _v11) (@Sigma.mk.{0, 0} (@Nat) (fun (_v14 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v14)) _v10 _v12)))) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v1) _v2 (@Eq.rec.{(0 + 1), (0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v9 _v10) (fun (_v14 :
  (@Nat)) =>
(fun (_v15 : (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v9 _v10) _v14)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v14))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v9 _v10 _v11 _v12)
  _v1 _v13)) (@And (@Ne.{(0 + 1)} (@Nat) _v10 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v9 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@And (@LE.le.{0} (@Nat) (@instLENat)
  _v8 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp3.Complexity.Uniform.V1.FixedPairParser.clock _v1) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))))) (@And (@Eq.{(0 + 1)}
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3 _v8 _v6) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v4)
  (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@CertificateGuardClosure.Target.Raw._proof_1 _v0 _v1)) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3 _v6))) (@Eq.{(0 + 1)} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v9 _v10 _v11 _v12)
  (@Bool.false))))))))))))))))) (@Exists.{(0 + 1)} (@Nat) (fun (_v9 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v10 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v9) (fun (_v11 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v9))
  =>
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v10) (fun (_v12 : (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v10)) =>
(@Exists.{0} (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v9 _v10) _v1) (fun (_v13 :
  (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v9 _v10) _v1)) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.decodePair _v1 _v2) (@Option.some.{0} (@Prod.{0, 0} (@Sigma.{0, 0} (@Nat) (fun
  (_v14 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v14))) (@Sigma.{0, 0} (@Nat) (fun (_v14 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v14)))) (@Prod.mk.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v14 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v14))) (@Sigma.{0, 0} (@Nat) (fun (_v14 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v14))) (@Sigma.mk.{0, 0} (@Nat) (fun (_v14 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v14)) _v9 _v11) (@Sigma.mk.{0, 0} (@Nat) (fun (_v14 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v14)) _v10 _v12)))) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v1) _v2 (@Eq.rec.{(0 + 1), (0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v9 _v10) (fun (_v14 :
  (@Nat)) =>
(fun (_v15 : (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v9 _v10) _v14)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v14))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v9 _v10 _v11 _v12)
  _v1 _v13)) (@And (@Eq.{(0 + 1)} (@Nat) _v10 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v9 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Exists.{(0 + 1)} (@Nat) (fun (_v14
  : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v15 : (@Nat)) =>
(@And (@Eq.{(0 + 1)} (@Nat) _v8 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14
  _v15)) (@And (@LE.le.{0} (@Nat) (@instLENat) _v14 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.FixedPairParser.clock _v1) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) (@HPow.hPow.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))))) (@And (∀ (_v16 : (@Nat)),
(∀ (_v17 : (@LT.lt.{0} (@Nat) (@instLTNat) _v16 _v14)),
(@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4)
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3 _v16 _v6))) (@OfNat.ofNat.{0} (@Nat) (77 : Nat) (@instOfNatNat
  (77 : Nat)))))) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3
  _v14 _v6) (@CertificateGuardClosure.config _v0 _v1 _v3 _v7)) (@And (∀ (_v16 : (@Nat)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v14 _v16) _v6) (@CertificateGuardClosure.config _v0 _v1 _v3 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  _v5 _v1 _v3 _v16 _v7)))) (@And (let _v16 : (@Nat) := (@TotalIngressClosure.allocation _v0 _v1);
(let _v17 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation _v1);
(let _v18 : (@Pnp3.Complexity.Uniform.V1.UniformTM) := (@TotalIngressClosure.machine _v0);
(let _v19 : (@Pnp3.Complexity.Uniform.V1.UniformTM) := (@BodyIngress.machine _v0);
(let _v20 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v18) _v1 _v16) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v18 _v1 _v16 _v2);
(let _v21 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v19) _v1 _v17) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v19 _v1 _v17 _v2);
(let _v22 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v19) _v1 _v16) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v19 _v1 _v16 _v2);
(@And (@LE.le.{0} (@Nat) (@instLENat) _v15 (@TotalIngressClosure.deadline _v0 _v1)) (@And (∀ (_v23 : (@Nat)),
(∀ (_v24 : (@LE.le.{0} (@Nat) (@instLENat) _v23 _v15)),
(@LE.le.{0} (@Nat) (@instLENat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v16)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v18) _v1 _v16
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v18 _v1 _v16 _v23 _v20))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))) (@HPow.hPow.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))))) (@And (∀ (_v23 : (@Nat)),
(∀ (_v24 : (@LE.le.{0} (@Nat) (@instLENat) _v23 _v15)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v18)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v18) _v1 _v16 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v18 _v1
  _v16 _v23 _v20)) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v18)))) (@And (∀ (_v23 : (@Nat)),
(∀ (_v24 : (@LT.lt.{0} (@Nat) (@instLTNat) _v23 _v15)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v18))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v18) _v1 _v16
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v18 _v1 _v16 _v23 _v20)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject
  _v18)) (@And (∀ (_v25 : (@Bool)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v18)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v18) _v1 _v16 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v18 _v1
  _v16 _v23 _v20)) (@TotalIngressClosure.old _v0 (@BodyIngress.old _v0 (@CarryWindow.embed _v0 (@CanonicalLeaf.result _v0
  _v25)))))) (∀ (_v25 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v18)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v18) _v1 _v16 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v18 _v1
  _v16 _v23 _v20)) (@TotalIngressClosure.old _v0 (@BodyIngress.body _v0 (@SerializedBody.entry _v25))))))))) (@Or (@And
  (@Eq.{(0 + 1)} (@Option.{0} (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.decodePair _v1 _v2) (@Option.none.{0}
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))) (@And (@Eq.{(0 + 1)} (@Nat) _v15
  (@Pnp3.Complexity.Uniform.V1.FixedPairParser.clock _v1)) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v18) _v1 _v16) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v18 _v1
  _v16 _v15 _v20) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v18) _v1 _v16
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v18) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v16)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@CertificateGuardClosure.Target.Frontier._proof_1 _v0
  _v1)) (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v18) _v1 _v16 _v20)))
  (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.encodedRelationLanguage
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0) _v1 _v2) (@Bool.false)))))
  (@Exists.{(0 + 1)} (@Nat) (fun (_v23 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v24 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v23) (fun (_v25 : (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v23)) =>
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v24) (fun (_v26 : (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v24)) =>
(@Exists.{0} (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v23 _v24) _v1) (fun (_v27 :
  (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v23 _v24) _v1)) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Pnp3.Complexity.Uniform.V1.PairEncoding.DecodedPair))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.decodePair _v1 _v2) (@Option.some.{0} (@Prod.{0, 0} (@Sigma.{0, 0} (@Nat) (fun
  (_v28 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v28))) (@Sigma.{0, 0} (@Nat) (fun (_v28 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v28)))) (@Prod.mk.{0, 0} (@Sigma.{0, 0} (@Nat) (fun (_v28 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v28))) (@Sigma.{0, 0} (@Nat) (fun (_v28 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v28))) (@Sigma.mk.{0, 0} (@Nat) (fun (_v28 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v28)) _v23 _v25) (@Sigma.mk.{0, 0} (@Nat) (fun (_v28 : (@Nat)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v28)) _v24 _v26)))) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring
  _v1) _v2 (@Eq.rec.{(0 + 1), (0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v23 _v24) (fun (_v28 :
  (@Nat)) =>
(fun (_v29 : (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v23 _v24) _v28)) =>
(@Pnp3.Complexity.Uniform.V1.Bitstring _v28))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v23 _v24 _v25 _v26)
  _v1 _v27)) (@Exists.{(0 + 1)} (@Nat) (fun (_v28 : (@Nat)) =>
(@And (@Eq.{(0 + 1)} (@Nat) _v15 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp3.Complexity.Uniform.V1.FixedPairParser.clock _v1) _v28)) (@And (∀ (_v29 : (@Nat)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v18) _v1 _v16)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v18 _v1 _v16 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.FixedPairParser.clock _v1) _v29) _v20) (@TotalIngressClosure.config
  _v0 _v1 _v16 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v19 _v1 _v16 _v29 _v22)))) (@Exists.{0} (@LE.le.{0} (@Nat)
  (@instLENat) _v17 _v16) (fun (_v29 : (@LE.le.{0} (@Nat) (@instLENat) _v17 _v16)) =>
(@And (@Pnp3.Complexity.Uniform.V1.FixedPairParser.ConfigExtension (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  _v19) _v1 _v17 _v16 _v29 _v21 _v22) (@And (∀ (_v30 : (@Nat)),
(∀ (_v31 : (@LE.le.{0} (@Nat) (@instLENat) _v30 _v28)),
(@LE.le.{0} (@Nat) (@instLENat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v17)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v19) _v1 _v17
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v19 _v1 _v17 _v30 (@Pnp3.Complexity.Uniform.V1.initialConfig _v19 _v1 _v17
  _v2)))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (12 :
  Nat) (@instOfNatNat (12 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat)))))))) (@And (∀ (_v30 : (@Nat)),
(∀ (_v31 : (@LT.lt.{0} (@Nat) (@instLTNat) _v30 _v28)),
(let _v32 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v19) _v1 _v17) :=
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v19 _v1 _v17 _v30 (@Pnp3.Complexity.Uniform.V1.initialConfig _v19 _v1 _v17
  _v2));
(∀ (_v33 : (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Move) (@Prod.snd.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move) (@Prod.snd.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v19))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step _v19
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v19) _v1 _v17 _v32)
  (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v19) _v1 _v17 _v32
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v19) _v1 _v17 _v32)))))
  (@Pnp3.Complexity.Uniform.V1.Move.right))),
(@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v17) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v19) _v1 _v17 _v32)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v17)))))) (@And (∀ (_v30 : (@Nat)),
(∀ (_v31 : (@LE.le.{0} (@Nat) (@instLENat) _v30 _v28)),
(@Pnp3.Complexity.Uniform.V1.FixedPairParser.ConfigExtension (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v19) _v1
  _v17 _v16 _v29 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v19 _v1 _v17 _v30 (@Pnp3.Complexity.Uniform.V1.initialConfig
  _v19 _v1 _v17 _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v19 _v1 _v16 _v30
  (@Pnp3.Complexity.Uniform.V1.initialConfig _v19 _v1 _v16 _v2))))) (@And (@Eq.{(0 + 1)}
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v18) _v1 _v16)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v18 _v1 _v16 _v15 _v20) (@TotalIngressClosure.config _v0 _v1 _v16
  (@IngressAllocation.extendConfig (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)) _v1 _v17
  _v16 _v29 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v19 _v1 _v17 _v28 _v21)))) (@Or (@And (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v19)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v19) _v1 _v17 (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v19 _v1
  _v17 _v28 _v21)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v19)) (@Eq.{(0 + 1)} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v23 _v24 _v25 _v26) (@Bool.false)))
  (@Exists.{(0 + 1)} (@Nat) (fun (_v30 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v31 : (@Nat)) =>
(@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v23 _v24) _v31) _v30) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v17)) (fun (_v32 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v23 _v24) _v31) _v30) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v17))) =>
(@And (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.tagMatches (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v23 _v24) (@Fin.append.{(0 + 1)} _v23 _v24 (@Bool) _v25 _v26))
  (@Bool.true)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Nat))
  (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros? (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v23 _v24) (@Fin.append.{(0 + 1)} _v23 _v24 (@Bool) _v25 _v26)) (@Option.some.{0}
  (@Nat) _v31)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Nat) (@Nat)))
  (@Pnp4.Frontier.ContractExpansion.contentHeader? (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v23 _v24) (@Fin.append.{(0 + 1)} _v23 _v24 (@Bool) _v25 _v26)) (@Option.some.{0} (@Prod.{0, 0} (@Nat)
  (@Nat)) (@Prod.mk.{0, 0} (@Nat) (@Nat) _v30 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v31) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))) (let _v33 :
  (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v23 _v24);
(let _v34 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v33 _v31) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))));
(let _v35 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v1);
(let _v36 : (@Nat) := (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0}
  (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v30);
(let _v37 : (@Nat) := (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v31)) _v36) _v33);
(let _v38 : (@Nat) := (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v33 _v37);
(let _v39 : (@Nat) := (@Cursor.Target.W _v0 _v30);
(let _v40 : (@Nat) := (@Cursor.Target.M _v0 _v30 _v31);
(let _v41 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v17)) := (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v1 _v17) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v33 _v31) _v30) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v32);
(let _v42 : (∀ (_v42 : (@Nat)),
(@Option.{0} (@Bool))) := (@Body.extend (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v23 _v24) _v17
  (@Body.installedTape (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v23 _v24) _v17 (@SmallIngress.prepared _v23
  _v24 _v17 _v25 _v26 _v31 _v30) _v34 _v30));
(let _v43 : (∀ (_v43 : (@Nat)),
(@Option.{0} (@Bool))) := (@Stream.Target.image _v42 _v33 _v31 _v30 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v31)) _v36 _v36 (@Bool.false));
(let _v44 : (∀ (_v44 : (@Nat)),
(@Option.{0} (@Bool))) := (@CappedWorkspace.Target.image (@SuffixCap.Target.image _v43 _v35 _v38) _v34 _v30 _v35 _v38);
(let _v45 : (∀ (_v45 : (@Nat)),
(@Option.{0} (@Bool))) := (@RuntimeBitLength.Target.fullImage _v44 _v34 _v30 _v35 _v38);
(let _v46 : (∀ (_v46 : (@Nat)),
(@Option.{0} (@Bool))) := (@AllArityBitLength.Target.seedImage _v45 _v35 _v38 _v30);
(let _v47 : (∀ (_v47 : (@Nat)),
(@Option.{0} (@Bool))) := (@CarryWindow.Target.image (@CappedWeight.Target.image _v46 _v34 _v30 _v35 _v38
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0}
  (@Nat) (@Nat.instMonoid))) _v30 _v0) _v0) _v39 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v35 _v38 _v30 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v30 _v0) _v0) (@Pnp4.Frontier.ContractExpansion.bitLength _v39)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) _v39);
(@And (@LT.lt.{0} (@Nat) (@instLTNat) _v30 (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.capacity _v23 _v24 _v31))
  (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v17) _v41) _v36) _v35) (@Or (@And (@LT.lt.{0} (@Nat) (@instLTNat)
  _v37 _v33) (@And (@LE.le.{0} (@Nat) (@instLENat) (@Pnp4.Frontier.ContractExpansion.bitLength _v30) _v38) (@And
  (@LE.le.{0} (@Nat) (@instLENat) _v39 _v38) (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter _v35 _v38
  _v30 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v17))
  (@And (∀ (_v48 : (@Nat)),
(∀ (_v49 : (@LE.le.{0} (@Nat) (@instLENat) _v40 _v48)),
(∀ (_v50 : (@LT.lt.{0} (@Nat) (@instLTNat) _v48 _v33)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v47 _v48) (@Option.some.{0} (@Bool) (@Fin.append.{(0 + 1)} _v23 _v24 (@Bool)
  _v25 _v26 (@Fin.mk (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v23 _v24) _v48
  _v50))))))) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v19)
  _v1 _v17) (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v19 _v1 _v17 _v28 _v21) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v19) _v1 _v17 (@BodyIngress.body _v0 (@SerializedBody.entry
  (@SerializedBody.sourceMode (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v23 _v24)
  (@Fin.append.{(0 + 1)} _v23 _v24 (@Bool) _v25 _v26) _v40))) _v41 (fun (_v48 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v17))) =>
(@SerializedBody.prepared _v47 _v33 _v40 _v35 _v38 _v30 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) _v30 _v0) _v0) _v39 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v17) _v48))))))))))
  (@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v30) (fun
  (_v48 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v30)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v33 _v40) (@And (∀ (_v49 : (@Fin _v39)),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v23 _v24) (@Fin.append.{(0 + 1)} _v23 _v24 (@Bool) _v25 _v26) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v40 (@Fin.val _v39 _v49))) (@Bool.false))) (@And (@Eq.{(0
  + 1)} (@Option.{0} (@Pnp3.Models.Circuit _v30)) (@Pnp4.Frontier.TreeCircuitWitnessCodec.decode
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v30 (fun (_v49 : (@Fin
  (@Pnp4.Frontier.TreeCircuitWitnessCodec.witnessBits (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v30)))
  =>
(@Bool.false))) (@Option.some.{0} (@Pnp3.Models.Circuit _v30) (@Pnp3.Models.Circuit.input _v30 (@Fin.mk _v30
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v48)))) (@Or (@And (@Eq.{(0 + 1)} (@Nat) _v37 _v33)
  (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v19) _v1 _v17)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v19 _v1 _v17 _v28 _v21) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v19) _v1 _v17 (@BodyIngress.old _v0 (@CarryWindow.embed _v0
  (@CanonicalLeaf.result _v0 (@Bool.false)))) _v41 (@Function.update.{(0 + 1), (0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v17)) (fun (_v49 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1
  _v17))) =>
(@Option.{0} (@Bool))) (@instDecidableEqFin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v17)) (fun (_v49 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v17))) =>
(@_v43 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v17) _v49))) _v41 (@Option.some.{0} (@Bool)
  (@Bool.false)))))) (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v37 _v33) (@And (@Or (@LT.lt.{0} (@Nat) (@instLTNat) _v38
  (@Pnp4.Frontier.ContractExpansion.bitLength _v30)) (@And (@LE.le.{0} (@Nat) (@instLENat)
  (@Pnp4.Frontier.ContractExpansion.bitLength _v30) _v38) (@Exists.{(0 + 1)} (@Nat) (fun (_v49 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v50 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v51 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v52 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v53 : (@Nat)) =>
(@Or (@Exists.{(0 + 1)} (@Nat) (fun (_v54 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v55 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v56 : (@Nat)) =>
(@And (@LT.lt.{0} (@Nat) (@instLTNat) _v54 _v0) (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v55 (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v30 _v54)) (@And
  (@LT.lt.{0} (@Nat) (@instLTNat) _v56 _v30) (@And (@Eq.{(0 + 1)} (@Nat) _v38 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  _v55 _v30) _v56)) (@And (@Eq.{(0 + 1)} (@Nat) _v49 (@Pnp4.Frontier.ContractExpansion.bitLength _v30)) (@And (@Eq.{(0 +
  1)} (@Nat) _v50 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HSub.hSub.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0}
  (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v30 _v54) _v55) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@And (@Eq.{(0 + 1)} (@Nat) _v51 _v38) (@And (@Eq.{(0 + 1)} (@Nat) _v52 (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Eq.{(0 + 1)} (@Nat) _v53 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v56 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))))))))))))))))
  (@Or (@Exists.{(0 + 1)} (@Nat) (fun (_v54 : (@Nat)) =>
(@And (@LT.lt.{0} (@Nat) (@instLTNat) _v54 _v0) (@And (@Eq.{(0 + 1)} (@Nat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v30 _v0) _v54) _v38) (@And (@Eq.{(0 + 1)} (@Nat) _v49
  (@Pnp4.Frontier.ContractExpansion.bitLength _v30)) (@And (@Eq.{(0 + 1)} (@Nat) _v50 _v38) (@And (@Eq.{(0 + 1)} (@Nat)
  _v51 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@And (@Eq.{(0 + 1)} (@Nat) _v52 (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Eq.{(0 + 1)} (@Nat) _v53 (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))))))))))) (@Or (@Exists.{(0 + 1)} (@Nat) (fun (_v54 : (@Nat)) =>
(@And (@LT.lt.{0} (@Nat) (@instLTNat) _v54 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@And (@Eq.{(0
  + 1)} (@Nat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp4.Frontier.ContractExpansion.bitLength _v30) _v54) _v38) (@And (@Eq.{(0 + 1)} (@Nat) _v49 _v38) (@And (@Eq.{(0 +
  1)} (@Nat) _v50 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v30 _v0) _v0))
  (@And (@Eq.{(0 + 1)} (@Nat) _v51 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@And (@Eq.{(0 + 1)}
  (@Nat) _v52 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Eq.{(0 + 1)} (@Nat) _v53 (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))))))))))) (@Exists.{(0 + 1)} (@Nat) (fun (_v54 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v55 : (@Nat)) =>
(@And (@LT.lt.{0} (@Nat) (@instLTNat) _v54 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@Pnp4.Frontier.ContractExpansion.bitLength _v30) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v55 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) _v30 _v0) _v0)) (@And (@Eq.{(0 + 1)} (@Nat) _v38 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  _v54 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v30 _v0) _v0)) _v55)) (@And
  (@Eq.{(0 + 1)} (@Nat) _v49 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat))
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp4.Frontier.ContractExpansion.bitLength _v30) (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))) _v54) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@And
  (@Eq.{(0 + 1)} (@Nat) _v50 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat))
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v30 _v0) _v0) _v55) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat))))) (@And (@Eq.{(0 + 1)} (@Nat) _v51 _v38) (@And (@Eq.{(0 + 1)} (@Nat) _v52 _v55) (@Eq.{(0 + 1)} (@Nat) _v53
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))))))))))))))))))))))))))))) (@Eq.{(0 + 1)}
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v19) _v1 _v17)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v19 _v1 _v17 _v28 _v21) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v19) _v1 _v17 (@BodyIngress.old _v0 (@CarryWindow.embed _v0
  (@CanonicalLeaf.result _v0 (@Bool.false)))) _v41 (@Function.update.{(0 + 1), (0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v17)) (fun (_v49 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1
  _v17))) =>
(@Option.{0} (@Bool))) (@instDecidableEqFin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v17)) (fun (_v49 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v17))) =>
(@Cursor.Target.image _v43 _v0 _v33 _v30 _v31 _v35 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v17) _v49)))
  _v41 (@Option.some.{0} (@Bool) (@Bool.false))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v4) _v1 _v3)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v4 _v1 _v3 _v8 _v6) (@CertificateGuardClosure.config _v0 _v1 _v3
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run _v5 _v1 _v3 _v15 _v7)))))))))))))))))))))))))))))))))))))))))) := by
  exact @CertificateGuardClosure.raw

-- Independent literal expected type for CertificateGuardClosure.wrong_length.
noncomputable def PartACanonical.Types.p0312 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v0)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v5 : (@Ne.{(0 + 1)} (@Nat) _v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v2 _v0 _v1 _v3
  _v4) (@Bool.false)))))))) := by
  exact @CertificateGuardClosure.wrong_length

-- Complete literal proposition for CertificateGuardClosure.wrong_length; original proof reused.
theorem PartACanonical.Surface.m0197 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v0)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v5 : (@Ne.{(0 + 1)} (@Nat) _v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v2 _v0 _v1 _v3
  _v4) (@Bool.false)))))))) := by
  exact @CertificateGuardClosure.wrong_length

-- Independent literal expected type for CertificateGuardClosure.wrong_length_mirror.
noncomputable def PartACanonical.Types.p0313 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v0)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v5 : (@Ne.{(0 + 1)} (@Nat) _v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v2 _v0 _v1 _v3
  _v4) (@Bool.false)))))))) := by
  exact @CertificateGuardClosure.wrong_length_mirror

-- Complete literal proposition for CertificateGuardClosure.wrong_length_mirror; original proof reused.
theorem PartACanonical.Surface.m0198 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v0)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v5 : (@Ne.{(0 + 1)} (@Nat) _v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v2 _v0 _v1 _v3
  _v4) (@Bool.false)))))))) := by
  exact @CertificateGuardClosure.wrong_length_mirror

-- Independent literal expected type for ConnectedRead.Exact.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0314 :
(∀ (_v0 : (@Nat)),
(Sort 0)))
end
-- Independent literal expected type for ConnectedRead.exact.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0315 :
(∀ (_v0 : (@Nat)),
(@ConnectedRead.Exact _v0)))
end
-- Independent literal expected type for Cursor.Boundary.EOF.
noncomputable def PartACanonical.Types.p0316 :
(∀ (_v0 : (@Nat)),
(Sort 0)) := by
  exact @Cursor.Boundary.EOF

-- Independent literal expected type for Cursor.Target.M.
noncomputable def PartACanonical.Types.p0317 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(@Nat)))) := by
  exact @Cursor.Target.M

-- Independent literal expected type for Cursor.Target.PartA.
noncomputable def PartACanonical.Types.p0318 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Pnp3.Complexity.Uniform.V1.UniformTM))),
(∀ (_v1 : (∀ (_v1 : (@Nat)),
(@Nat))),
(Sort 0))) := by
  exact @Cursor.Target.PartA

-- Independent literal expected type for Cursor.Target.Raw.
noncomputable def PartACanonical.Types.p0319 :
(∀ (_v0 : (@Nat)),
(Sort 0)) := by
  exact @Cursor.Target.Raw

-- Independent literal expected type for Cursor.Target.W.
noncomputable def PartACanonical.Types.p0320 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(@Nat))) := by
  exact @Cursor.Target.W
