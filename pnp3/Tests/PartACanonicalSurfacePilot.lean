import Tests.PartACanonicalABI
import Tests.PartAG2InterfaceTests

/-! Infrastructure: mechanical literal restatements of this exact original API.
Proof terms are reused; these are not independently authored correctness proofs.
Type pins, theorem mirrors and direct roots remain separate manifests. -/
set_option autoImplicit false

-- Independent literal expected type for AllArityBitLength.phase_row.
noncomputable def PartACanonical.Types.p0015 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Option.{0} (@Bool))),
(∀ (_v4 : (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (308 : Nat) (@instOfNatNat (308 : Nat))) _v1)),
(∀ (_v5 : (@LT.lt.{0} (@Nat) (@instLTNat) _v1 (@OfNat.ofNat.{0} (@Nat) (329 : Nat) (@instOfNatNat (329 : Nat))))),
(∀ (_v6 : (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@GetElem?.getElem?.{0, 0, 0} (@List.{0} (@Nat)) (@Nat) (@Nat) (fun (_v6 :
  (@List.{0} (@Nat))) =>
(fun (_v7 : (@Nat)) =>
(@LT.lt.{0} (@Nat) (@instLTNat) _v7 (@List.length.{0} (@Nat) _v6)))) (@List.instGetElem?NatLtLength.{0} (@Nat))
  (@AllArityBitLength.instructions _v0) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v1
  (@OfNat.ofNat.{0} (@Nat) (308 : Nat) (@instOfNatNat (308 : Nat))))) (@PartACanonical.PrivateABI.a0001.{(0 + 1)} (fun
  (_v6 : (@Option.{0} (@Bool))) =>
(@Nat)) _v3 (fun (_v6 : (@Unit)) =>
(@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (fun (_v6 : (@Unit)) =>
(@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (fun (_v6 : (@Unit)) =>
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
  (@Pnp3.Complexity.Uniform.V1.Move.stay) (@Pnp3.Complexity.Uniform.V1.Move.right))))))))))))) := by
  exact @AllArityBitLength.phase_row

-- Complete literal proposition for AllArityBitLength.phase_row; original proof reused.
theorem PartACanonical.Surface.m0009 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Option.{0} (@Bool))),
(∀ (_v4 : (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (308 : Nat) (@instOfNatNat (308 : Nat))) _v1)),
(∀ (_v5 : (@LT.lt.{0} (@Nat) (@instLTNat) _v1 (@OfNat.ofNat.{0} (@Nat) (329 : Nat) (@instOfNatNat (329 : Nat))))),
(∀ (_v6 : (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@GetElem?.getElem?.{0, 0, 0} (@List.{0} (@Nat)) (@Nat) (@Nat) (fun (_v6 :
  (@List.{0} (@Nat))) =>
(fun (_v7 : (@Nat)) =>
(@LT.lt.{0} (@Nat) (@instLTNat) _v7 (@List.length.{0} (@Nat) _v6)))) (@List.instGetElem?NatLtLength.{0} (@Nat))
  (@AllArityBitLength.instructions _v0) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v1
  (@OfNat.ofNat.{0} (@Nat) (308 : Nat) (@instOfNatNat (308 : Nat))))) (@PartACanonical.PrivateABI.a0001.{(0 + 1)} (fun
  (_v6 : (@Option.{0} (@Bool))) =>
(@Nat)) _v3 (fun (_v6 : (@Unit)) =>
(@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (fun (_v6 : (@Unit)) =>
(@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (fun (_v6 : (@Unit)) =>
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
  (@Pnp3.Complexity.Uniform.V1.Move.stay) (@Pnp3.Complexity.Uniform.V1.Move.right))))))))))))) := by
  exact @AllArityBitLength.phase_row

-- Independent literal expected type for AllArityBitLength.«tacticFromDonor___=>_».
noncomputable def PartACanonical.Types.p0018 :
(@Lean.ParserDescr) := by
  exact @AllArityBitLength.«tacticFromDonor___=>_»

-- Independent literal expected type for BitLengthDriver.phase_row.
noncomputable def PartACanonical.Types.p0073 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Option.{0} (@Bool))),
(∀ (_v4 : (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (201 : Nat) (@instOfNatNat (201 : Nat))) _v1)),
(∀ (_v5 : (@LT.lt.{0} (@Nat) (@instLTNat) _v1 (@OfNat.ofNat.{0} (@Nat) (308 : Nat) (@instOfNatNat (308 : Nat))))),
(∀ (_v6 : (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@GetElem?.getElem?.{0, 0, 0} (@List.{0} (@Nat)) (@Nat) (@Nat) (fun (_v6 :
  (@List.{0} (@Nat))) =>
(fun (_v7 : (@Nat)) =>
(@LT.lt.{0} (@Nat) (@instLTNat) _v7 (@List.length.{0} (@Nat) _v6)))) (@List.instGetElem?NatLtLength.{0} (@Nat))
  (@BitLengthDriver.instructions _v0) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v1
  (@OfNat.ofNat.{0} (@Nat) (201 : Nat) (@instOfNatNat (201 : Nat))))) (@PartACanonical.PrivateABI.a0002.{(0 + 1)} (fun
  (_v6 : (@Option.{0} (@Bool))) =>
(@Nat)) _v3 (fun (_v6 : (@Unit)) =>
(@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (fun (_v6 : (@Unit)) =>
(@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (fun (_v6 : (@Unit)) =>
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
  (@Pnp3.Complexity.Uniform.V1.Move.stay) (@Pnp3.Complexity.Uniform.V1.Move.right))))))))))))) := by
  exact @BitLengthDriver.phase_row

-- Complete literal proposition for BitLengthDriver.phase_row; original proof reused.
theorem PartACanonical.Surface.m0053 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Option.{0} (@Bool))),
(∀ (_v4 : (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (201 : Nat) (@instOfNatNat (201 : Nat))) _v1)),
(∀ (_v5 : (@LT.lt.{0} (@Nat) (@instLTNat) _v1 (@OfNat.ofNat.{0} (@Nat) (308 : Nat) (@instOfNatNat (308 : Nat))))),
(∀ (_v6 : (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@GetElem?.getElem?.{0, 0, 0} (@List.{0} (@Nat)) (@Nat) (@Nat) (fun (_v6 :
  (@List.{0} (@Nat))) =>
(fun (_v7 : (@Nat)) =>
(@LT.lt.{0} (@Nat) (@instLTNat) _v7 (@List.length.{0} (@Nat) _v6)))) (@List.instGetElem?NatLtLength.{0} (@Nat))
  (@BitLengthDriver.instructions _v0) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v1
  (@OfNat.ofNat.{0} (@Nat) (201 : Nat) (@instOfNatNat (201 : Nat))))) (@PartACanonical.PrivateABI.a0002.{(0 + 1)} (fun
  (_v6 : (@Option.{0} (@Bool))) =>
(@Nat)) _v3 (fun (_v6 : (@Unit)) =>
(@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (fun (_v6 : (@Unit)) =>
(@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (fun (_v6 : (@Unit)) =>
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
  (@Pnp3.Complexity.Uniform.V1.Move.stay) (@Pnp3.Complexity.Uniform.V1.Move.right))))))))))))) := by
  exact @BitLengthDriver.phase_row

-- Independent literal expected type for BitLengthDriver.«tacticFromH_=>_».
noncomputable def PartACanonical.Types.p0076 :
(@Lean.ParserDescr) := by
  exact @BitLengthDriver.«tacticFromH_=>_»

-- Independent literal expected type for Body.Node.rec.
section
universe u
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0103 :
(∀ {_v0 : (∀ (_v0 : (@Body.Node)),
(Sort u))},
(∀ (_v1 : (∀ (_v1 : (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))))),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (∀ (_v3 : (@Nat)),
(@Option.{0} (@Bool)))),
(@_v0 (@Body.Node.mk _v1 _v2 _v3)))))),
(∀ (_v2 : (@Body.Node)),
(@_v0 _v2)))))
end
-- Independent literal expected type for Body.Path.rec.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0119 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Body.Node)),
(∀ (_v3 : (@Body.Node)),
(∀ (_v4 : (@Body.Path _v0 _v1 _v2 _v3)),
(Sort 0)))))},
(∀ (_v2 : (∀ (_v2 : (@Body.Node)),
(∀ (_v3 : (@LE.le.{0} (@Nat) (@instLENat) (@Body.Node.head _v2) _v0)),
(@_v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v2 _v2 (@Body.Path.nil _v0 _v2 _v3))))),
(∀ (_v3 : (∀ {_v3 : (@Nat)},
(∀ {_v4 : (@Body.Node)},
(∀ {_v5 : (@Body.Node)},
(∀ {_v6 : (@Body.Node)},
(∀ (_v7 : (@Body.Edge _v0 _v4 _v5)),
(∀ (_v8 : (@Body.Path _v0 _v3 _v5 _v6)),
(∀ (_v9 : (@_v1 _v3 _v5 _v6 _v8)),
(@_v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@OfNat.ofNat.{0} (@Nat) (1 :
  Nat) (@instOfNatNat (1 : Nat)))) _v4 _v6 (@Body.Path.cons _v0 _v3 _v4 _v5 _v6 _v7 _v8)))))))))),
(∀ {_v4 : (@Nat)},
(∀ {_v5 : (@Body.Node)},
(∀ {_v6 : (@Body.Node)},
(∀ (_v7 : (@Body.Path _v0 _v4 _v5 _v6)),
(@_v1 _v4 _v5 _v6 _v7))))))))))
end
-- Independent literal expected type for BodyIngress.body.
noncomputable def PartACanonical.Types.p0198 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)))),
(@Fin (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@CarryWindow.machine _v0)) (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))))
  (@PartACanonical.PrivateABI.a0003))))) := by
  exact @BodyIngress.body

-- Independent literal expected type for BodyIngress.body_rows.
noncomputable def PartACanonical.Types.p0200 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)))),
(∀ (_v2 : (@Option.{0} (@Bool))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step
  (@BodyIngress.machine _v0) (@BodyIngress.body _v0 _v1) _v2) (@Prod.mk.{0, 0} (@Fin (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)) (@OfNat.ofNat.{0} (@Nat)
  (7500 : Nat) (@instOfNatNat (7500 : Nat)))) (@PartACanonical.PrivateABI.a0003))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@BodyIngress.body _v0 (@Prod.fst.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@SerializedBody.machine) _v1 _v2)))
  (@Prod.snd.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step
  (@SerializedBody.machine) _v1 _v2))))))) := by
  exact @BodyIngress.body_rows

-- Complete literal proposition for BodyIngress.body_rows; original proof reused.
theorem PartACanonical.Surface.m0120 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)))),
(∀ (_v2 : (@Option.{0} (@Bool))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step
  (@BodyIngress.machine _v0) (@BodyIngress.body _v0 _v1) _v2) (@Prod.mk.{0, 0} (@Fin (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)) (@OfNat.ofNat.{0} (@Nat)
  (7500 : Nat) (@instOfNatNat (7500 : Nat)))) (@PartACanonical.PrivateABI.a0003))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@BodyIngress.body _v0 (@Prod.fst.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@SerializedBody.machine) _v1 _v2)))
  (@Prod.snd.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step
  (@SerializedBody.machine) _v1 _v2))))))) := by
  exact @BodyIngress.body_rows

-- Independent literal expected type for BodyIngress.check_body_rows.
noncomputable def PartACanonical.Types.p0202 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)))),
(∀ (_v2 : (@Option.{0} (@Bool))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step
  (@BodyIngress.machine _v0) (@BodyIngress.body _v0 _v1) _v2) (@Prod.mk.{0, 0} (@Fin (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)) (@OfNat.ofNat.{0} (@Nat)
  (7500 : Nat) (@instOfNatNat (7500 : Nat)))) (@PartACanonical.PrivateABI.a0003))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@BodyIngress.body _v0 (@Prod.fst.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@SerializedBody.machine) _v1 _v2)))
  (@Prod.snd.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step
  (@SerializedBody.machine) _v1 _v2))))))) := by
  exact @BodyIngress.check_body_rows

-- Complete literal proposition for BodyIngress.check_body_rows; original proof reused.
theorem PartACanonical.Surface.m0122 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)))),
(∀ (_v2 : (@Option.{0} (@Bool))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step
  (@BodyIngress.machine _v0) (@BodyIngress.body _v0 _v1) _v2) (@Prod.mk.{0, 0} (@Fin (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)) (@OfNat.ofNat.{0} (@Nat)
  (7500 : Nat) (@instOfNatNat (7500 : Nat)))) (@PartACanonical.PrivateABI.a0003))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@BodyIngress.body _v0 (@Prod.fst.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@SerializedBody.machine) _v1 _v2)))
  (@Prod.snd.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine))) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step
  (@SerializedBody.machine) _v1 _v2))))))) := by
  exact @BodyIngress.check_body_rows

-- Independent literal expected type for BodyIngress.check_embeddings.
noncomputable def PartACanonical.Types.p0204 :
(∀ (_v0 : (@Nat)),
(@And (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine
  _v0)) (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2035 : Nat)
  (@instOfNatNat (2035 : Nat))))) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@BodyIngress.machine _v0))) (@Pnp3.Complexity.Uniform.V1.UniformTM.start (@BodyIngress.machine _v0)) (@BodyIngress.old
  _v0 (@Pnp3.Complexity.Uniform.V1.UniformTM.start (@CarryWindow.machine _v0)))) (@And (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@BodyIngress.machine _v0)) (@BodyIngress.old _v0
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@CarryWindow.machine _v0)))) (@And (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@BodyIngress.machine _v0)) (@BodyIngress.old _v0
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@CarryWindow.machine _v0)))) (@And (@Function.Injective.{(0 + 1), (0 +
  1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))) (@Fin (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)) (@OfNat.ofNat.{0}
  (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat)))) (@PartACanonical.PrivateABI.a0003))) (@BodyIngress.old _v0)) (@And
  (@Function.Injective.{(0 + 1), (0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine))) (@Fin (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)) (@OfNat.ofNat.{0} (@Nat) (7500 : Nat)
  (@instOfNatNat (7500 : Nat)))) (@PartACanonical.PrivateABI.a0003))) (@BodyIngress.body _v0)) (∀ (_v1 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)))),
(∀ (_v2 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(@Ne.{(0 + 1)} (@Fin (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@CarryWindow.machine _v0)) (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))))
  (@PartACanonical.PrivateABI.a0003))) (@BodyIngress.old _v0 _v1) (@BodyIngress.body _v0 (@SerializedBody.entry
  _v2)))))))))))) := by
  exact @BodyIngress.check_embeddings

-- Complete literal proposition for BodyIngress.check_embeddings; original proof reused.
theorem PartACanonical.Surface.m0124 :
(∀ (_v0 : (@Nat)),
(@And (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine
  _v0)) (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2035 : Nat)
  (@instOfNatNat (2035 : Nat))))) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@BodyIngress.machine _v0))) (@Pnp3.Complexity.Uniform.V1.UniformTM.start (@BodyIngress.machine _v0)) (@BodyIngress.old
  _v0 (@Pnp3.Complexity.Uniform.V1.UniformTM.start (@CarryWindow.machine _v0)))) (@And (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@BodyIngress.machine _v0)) (@BodyIngress.old _v0
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@CarryWindow.machine _v0)))) (@And (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@BodyIngress.machine _v0)) (@BodyIngress.old _v0
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@CarryWindow.machine _v0)))) (@And (@Function.Injective.{(0 + 1), (0 +
  1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))) (@Fin (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)) (@OfNat.ofNat.{0}
  (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat)))) (@PartACanonical.PrivateABI.a0003))) (@BodyIngress.old _v0)) (@And
  (@Function.Injective.{(0 + 1), (0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine))) (@Fin (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)) (@OfNat.ofNat.{0} (@Nat) (7500 : Nat)
  (@instOfNatNat (7500 : Nat)))) (@PartACanonical.PrivateABI.a0003))) (@BodyIngress.body _v0)) (∀ (_v1 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)))),
(∀ (_v2 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(@Ne.{(0 + 1)} (@Fin (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@CarryWindow.machine _v0)) (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))))
  (@PartACanonical.PrivateABI.a0003))) (@BodyIngress.old _v0 _v1) (@BodyIngress.body _v0 (@SerializedBody.entry
  _v2)))))))))))) := by
  exact @BodyIngress.check_embeddings

-- Independent literal expected type for BodyIngress.check_table_delta.
noncomputable def PartACanonical.Types.p0208 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)))),
(∀ (_v2 : (@Option.{0} (@Bool))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step
  (@BodyIngress.machine _v0) (@BodyIngress.old _v0 _v1) _v2) (@ite.{(0 + 1)} (@Prod.{0, 0} (@Fin (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)) (@OfNat.ofNat.{0}
  (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat)))) (@PartACanonical.PrivateABI.a0003))) (@Prod.{0, 0} (@Option.{0}
  (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@And (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))) _v1 (@CarryWindow.ready _v0)) (@Eq.{(0 +
  1)} (@Option.{0} (@Bool)) _v2 (@Option.none.{0} (@Bool)))) (@instDecidableAnd (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))) _v1 (@CarryWindow.ready _v0)) (@Eq.{(0 +
  1)} (@Option.{0} (@Bool)) _v2 (@Option.none.{0} (@Bool))) (@instDecidableEqFin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)) _v1 (@CarryWindow.ready _v0))
  (@Option.instDecidableEq.{0} (@Bool) (@instDecidableEqBool) _v2 (@Option.none.{0} (@Bool)))) (@Prod.mk.{0, 0} (@Fin
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine
  _v0)) (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat)))) (@PartACanonical.PrivateABI.a0003)))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@BodyIngress.extra _v0 (@Fin.mk
  (@PartACanonical.PrivateABI.a0003) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@of_decide_eq_true
  (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@PartACanonical.PrivateABI.a0003)) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@PartACanonical.PrivateABI.a0003)) (@id.{0} (@Eq.{(0 + 1)} (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat) (@instLTNat)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@PartACanonical.PrivateABI.a0003)) (@Nat.decLt
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@PartACanonical.PrivateABI.a0003))) (@Bool.true))
  (@Eq.refl.{(0 + 1)} (@Bool) (@Bool.true)))))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)
  (@Option.none.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move.stay))) (@Prod.mk.{0, 0} (@Fin (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)) (@OfNat.ofNat.{0} (@Nat)
  (7500 : Nat) (@instOfNatNat (7500 : Nat)))) (@PartACanonical.PrivateABI.a0003))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@BodyIngress.old _v0 (@Prod.fst.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@CarryWindow.machine _v0) _v1 _v2)))
  (@Prod.snd.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step
  (@CarryWindow.machine _v0) _v1 _v2)))))))) := by
  exact @BodyIngress.check_table_delta

-- Complete literal proposition for BodyIngress.check_table_delta; original proof reused.
theorem PartACanonical.Surface.m0128 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)))),
(∀ (_v2 : (@Option.{0} (@Bool))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step
  (@BodyIngress.machine _v0) (@BodyIngress.old _v0 _v1) _v2) (@ite.{(0 + 1)} (@Prod.{0, 0} (@Fin (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)) (@OfNat.ofNat.{0}
  (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat)))) (@PartACanonical.PrivateABI.a0003))) (@Prod.{0, 0} (@Option.{0}
  (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@And (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))) _v1 (@CarryWindow.ready _v0)) (@Eq.{(0 +
  1)} (@Option.{0} (@Bool)) _v2 (@Option.none.{0} (@Bool)))) (@instDecidableAnd (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))) _v1 (@CarryWindow.ready _v0)) (@Eq.{(0 +
  1)} (@Option.{0} (@Bool)) _v2 (@Option.none.{0} (@Bool))) (@instDecidableEqFin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)) _v1 (@CarryWindow.ready _v0))
  (@Option.instDecidableEq.{0} (@Bool) (@instDecidableEqBool) _v2 (@Option.none.{0} (@Bool)))) (@Prod.mk.{0, 0} (@Fin
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine
  _v0)) (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat)))) (@PartACanonical.PrivateABI.a0003)))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@BodyIngress.extra _v0 (@Fin.mk
  (@PartACanonical.PrivateABI.a0003) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@of_decide_eq_true
  (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@PartACanonical.PrivateABI.a0003)) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@PartACanonical.PrivateABI.a0003)) (@id.{0} (@Eq.{(0 + 1)} (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat) (@instLTNat)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@PartACanonical.PrivateABI.a0003)) (@Nat.decLt
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@PartACanonical.PrivateABI.a0003))) (@Bool.true))
  (@Eq.refl.{(0 + 1)} (@Bool) (@Bool.true)))))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)
  (@Option.none.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move.stay))) (@Prod.mk.{0, 0} (@Fin (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)) (@OfNat.ofNat.{0} (@Nat)
  (7500 : Nat) (@instOfNatNat (7500 : Nat)))) (@PartACanonical.PrivateABI.a0003))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@BodyIngress.old _v0 (@Prod.fst.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@CarryWindow.machine _v0) _v1 _v2)))
  (@Prod.snd.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step
  (@CarryWindow.machine _v0) _v1 _v2)))))))) := by
  exact @BodyIngress.check_table_delta

-- Independent literal expected type for BodyIngress.embeddings.
noncomputable def PartACanonical.Types.p0214 :
(∀ (_v0 : (@Nat)),
(@And (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine
  _v0)) (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2035 : Nat)
  (@instOfNatNat (2035 : Nat))))) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@BodyIngress.machine _v0))) (@Pnp3.Complexity.Uniform.V1.UniformTM.start (@BodyIngress.machine _v0)) (@BodyIngress.old
  _v0 (@Pnp3.Complexity.Uniform.V1.UniformTM.start (@CarryWindow.machine _v0)))) (@And (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@BodyIngress.machine _v0)) (@BodyIngress.old _v0
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@CarryWindow.machine _v0)))) (@And (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@BodyIngress.machine _v0)) (@BodyIngress.old _v0
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@CarryWindow.machine _v0)))) (@And (@Function.Injective.{(0 + 1), (0 +
  1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))) (@Fin (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)) (@OfNat.ofNat.{0}
  (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat)))) (@PartACanonical.PrivateABI.a0003))) (@BodyIngress.old _v0)) (@And
  (@Function.Injective.{(0 + 1), (0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine))) (@Fin (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)) (@OfNat.ofNat.{0} (@Nat) (7500 : Nat)
  (@instOfNatNat (7500 : Nat)))) (@PartACanonical.PrivateABI.a0003))) (@BodyIngress.body _v0)) (∀ (_v1 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)))),
(∀ (_v2 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(@Ne.{(0 + 1)} (@Fin (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@CarryWindow.machine _v0)) (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))))
  (@PartACanonical.PrivateABI.a0003))) (@BodyIngress.old _v0 _v1) (@BodyIngress.body _v0 (@SerializedBody.entry
  _v2)))))))))))) := by
  exact @BodyIngress.embeddings

-- Complete literal proposition for BodyIngress.embeddings; original proof reused.
theorem PartACanonical.Surface.m0133 :
(∀ (_v0 : (@Nat)),
(@And (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine
  _v0)) (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2035 : Nat)
  (@instOfNatNat (2035 : Nat))))) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@BodyIngress.machine _v0))) (@Pnp3.Complexity.Uniform.V1.UniformTM.start (@BodyIngress.machine _v0)) (@BodyIngress.old
  _v0 (@Pnp3.Complexity.Uniform.V1.UniformTM.start (@CarryWindow.machine _v0)))) (@And (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@BodyIngress.machine _v0)) (@BodyIngress.old _v0
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@CarryWindow.machine _v0)))) (@And (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@BodyIngress.machine _v0)) (@BodyIngress.old _v0
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@CarryWindow.machine _v0)))) (@And (@Function.Injective.{(0 + 1), (0 +
  1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))) (@Fin (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)) (@OfNat.ofNat.{0}
  (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat)))) (@PartACanonical.PrivateABI.a0003))) (@BodyIngress.old _v0)) (@And
  (@Function.Injective.{(0 + 1), (0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine))) (@Fin (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)) (@OfNat.ofNat.{0} (@Nat) (7500 : Nat)
  (@instOfNatNat (7500 : Nat)))) (@PartACanonical.PrivateABI.a0003))) (@BodyIngress.body _v0)) (∀ (_v1 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)))),
(∀ (_v2 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(@Ne.{(0 + 1)} (@Fin (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@CarryWindow.machine _v0)) (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))))
  (@PartACanonical.PrivateABI.a0003))) (@BodyIngress.old _v0 _v1) (@BodyIngress.body _v0 (@SerializedBody.entry
  _v2)))))))))))) := by
  exact @BodyIngress.embeddings

-- Independent literal expected type for BodyIngress.extra.
noncomputable def PartACanonical.Types.p0215 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@PartACanonical.PrivateABI.a0003))),
(@Fin (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@CarryWindow.machine _v0)) (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))))
  (@PartACanonical.PrivateABI.a0003))))) := by
  exact @BodyIngress.extra

-- Independent literal expected type for BodyIngress.old.
noncomputable def PartACanonical.Types.p0218 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)))),
(@Fin (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@CarryWindow.machine _v0)) (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))))
  (@PartACanonical.PrivateABI.a0003))))) := by
  exact @BodyIngress.old

-- Independent literal expected type for BodyIngress.table_delta.
noncomputable def PartACanonical.Types.p0221 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)))),
(∀ (_v2 : (@Option.{0} (@Bool))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step
  (@BodyIngress.machine _v0) (@BodyIngress.old _v0 _v1) _v2) (@ite.{(0 + 1)} (@Prod.{0, 0} (@Fin (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)) (@OfNat.ofNat.{0}
  (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat)))) (@PartACanonical.PrivateABI.a0003))) (@Prod.{0, 0} (@Option.{0}
  (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@And (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))) _v1 (@CarryWindow.ready _v0)) (@Eq.{(0 +
  1)} (@Option.{0} (@Bool)) _v2 (@Option.none.{0} (@Bool)))) (@instDecidableAnd (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))) _v1 (@CarryWindow.ready _v0)) (@Eq.{(0 +
  1)} (@Option.{0} (@Bool)) _v2 (@Option.none.{0} (@Bool))) (@instDecidableEqFin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)) _v1 (@CarryWindow.ready _v0))
  (@Option.instDecidableEq.{0} (@Bool) (@instDecidableEqBool) _v2 (@Option.none.{0} (@Bool)))) (@Prod.mk.{0, 0} (@Fin
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine
  _v0)) (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat)))) (@PartACanonical.PrivateABI.a0003)))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@BodyIngress.extra _v0 (@Fin.mk
  (@PartACanonical.PrivateABI.a0003) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@of_decide_eq_true
  (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@PartACanonical.PrivateABI.a0003)) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@PartACanonical.PrivateABI.a0003)) (@id.{0} (@Eq.{(0 + 1)} (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat) (@instLTNat)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@PartACanonical.PrivateABI.a0003)) (@Nat.decLt
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@PartACanonical.PrivateABI.a0003))) (@Bool.true))
  (@Eq.refl.{(0 + 1)} (@Bool) (@Bool.true)))))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)
  (@Option.none.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move.stay))) (@Prod.mk.{0, 0} (@Fin (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)) (@OfNat.ofNat.{0} (@Nat)
  (7500 : Nat) (@instOfNatNat (7500 : Nat)))) (@PartACanonical.PrivateABI.a0003))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@BodyIngress.old _v0 (@Prod.fst.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@CarryWindow.machine _v0) _v1 _v2)))
  (@Prod.snd.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step
  (@CarryWindow.machine _v0) _v1 _v2)))))))) := by
  exact @BodyIngress.table_delta

-- Complete literal proposition for BodyIngress.table_delta; original proof reused.
theorem PartACanonical.Surface.m0137 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)))),
(∀ (_v2 : (@Option.{0} (@Bool))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step
  (@BodyIngress.machine _v0) (@BodyIngress.old _v0 _v1) _v2) (@ite.{(0 + 1)} (@Prod.{0, 0} (@Fin (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)) (@OfNat.ofNat.{0}
  (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat)))) (@PartACanonical.PrivateABI.a0003))) (@Prod.{0, 0} (@Option.{0}
  (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@And (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))) _v1 (@CarryWindow.ready _v0)) (@Eq.{(0 +
  1)} (@Option.{0} (@Bool)) _v2 (@Option.none.{0} (@Bool)))) (@instDecidableAnd (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))) _v1 (@CarryWindow.ready _v0)) (@Eq.{(0 +
  1)} (@Option.{0} (@Bool)) _v2 (@Option.none.{0} (@Bool))) (@instDecidableEqFin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)) _v1 (@CarryWindow.ready _v0))
  (@Option.instDecidableEq.{0} (@Bool) (@instDecidableEqBool) _v2 (@Option.none.{0} (@Bool)))) (@Prod.mk.{0, 0} (@Fin
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine
  _v0)) (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat)))) (@PartACanonical.PrivateABI.a0003)))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@BodyIngress.extra _v0 (@Fin.mk
  (@PartACanonical.PrivateABI.a0003) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@of_decide_eq_true
  (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@PartACanonical.PrivateABI.a0003)) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@PartACanonical.PrivateABI.a0003)) (@id.{0} (@Eq.{(0 + 1)} (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat) (@instLTNat)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@PartACanonical.PrivateABI.a0003)) (@Nat.decLt
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@PartACanonical.PrivateABI.a0003))) (@Bool.true))
  (@Eq.refl.{(0 + 1)} (@Bool) (@Bool.true)))))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)
  (@Option.none.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move.stay))) (@Prod.mk.{0, 0} (@Fin (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)) (@OfNat.ofNat.{0} (@Nat)
  (7500 : Nat) (@instOfNatNat (7500 : Nat)))) (@PartACanonical.PrivateABI.a0003))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@BodyIngress.old _v0 (@Prod.fst.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@CarryWindow.machine _v0) _v1 _v2)))
  (@Prod.snd.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step
  (@CarryWindow.machine _v0) _v1 _v2)))))))) := by
  exact @BodyIngress.table_delta

-- Independent literal expected type for CappedWeight.phase_row.
noncomputable def PartACanonical.Types.p0260 :
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
  (@OfNat.ofNat.{0} (@Nat) (329 : Nat) (@instOfNatNat (329 : Nat))))) (@PartACanonical.PrivateABI.a0004.{(0 + 1)} (fun
  (_v7 : (@Option.{0} (@Bool))) =>
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
  exact @CappedWeight.phase_row

-- Complete literal proposition for CappedWeight.phase_row; original proof reused.
theorem PartACanonical.Surface.m0165 :
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
  (@OfNat.ofNat.{0} (@Nat) (329 : Nat) (@instOfNatNat (329 : Nat))))) (@PartACanonical.PrivateABI.a0004.{(0 + 1)} (fun
  (_v7 : (@Option.{0} (@Bool))) =>
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
  exact @CappedWeight.phase_row

-- Independent literal expected type for CappedWorkspace.setup_row.
noncomputable def PartACanonical.Types.p0269 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Option.{0} (@Bool))),
(∀ (_v4 : (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (98 : Nat) (@instOfNatNat (98 : Nat))) _v1)),
(∀ (_v5 : (@LT.lt.{0} (@Nat) (@instLTNat) _v1 (@OfNat.ofNat.{0} (@Nat) (201 : Nat) (@instOfNatNat (201 : Nat))))),
(∀ (_v6 : (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@GetElem?.getElem?.{0, 0, 0} (@List.{0} (@Nat)) (@Nat) (@Nat) (fun (_v6 :
  (@List.{0} (@Nat))) =>
(fun (_v7 : (@Nat)) =>
(@LT.lt.{0} (@Nat) (@instLTNat) _v7 (@List.length.{0} (@Nat) _v6)))) (@List.instGetElem?NatLtLength.{0} (@Nat))
  (@CappedWorkspace.instructions) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v1
  (@OfNat.ofNat.{0} (@Nat) (98 : Nat) (@instOfNatNat (98 : Nat))))) (@PartACanonical.PrivateABI.a0014.{(0 + 1)} (fun (_v6
  : (@Option.{0} (@Bool))) =>
(@Nat)) _v3 (fun (_v6 : (@Unit)) =>
(@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (fun (_v6 : (@Unit)) =>
(@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (fun (_v6 : (@Unit)) =>
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
  (@Pnp3.Complexity.Uniform.V1.Move.stay) (@Pnp3.Complexity.Uniform.V1.Move.right))))))))))))) := by
  exact @CappedWorkspace.setup_row

-- Complete literal proposition for CappedWorkspace.setup_row; original proof reused.
theorem PartACanonical.Surface.m0170 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Option.{0} (@Bool))),
(∀ (_v4 : (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (98 : Nat) (@instOfNatNat (98 : Nat))) _v1)),
(∀ (_v5 : (@LT.lt.{0} (@Nat) (@instLTNat) _v1 (@OfNat.ofNat.{0} (@Nat) (201 : Nat) (@instOfNatNat (201 : Nat))))),
(∀ (_v6 : (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@GetElem?.getElem?.{0, 0, 0} (@List.{0} (@Nat)) (@Nat) (@Nat) (fun (_v6 :
  (@List.{0} (@Nat))) =>
(fun (_v7 : (@Nat)) =>
(@LT.lt.{0} (@Nat) (@instLTNat) _v7 (@List.length.{0} (@Nat) _v6)))) (@List.instGetElem?NatLtLength.{0} (@Nat))
  (@CappedWorkspace.instructions) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v1
  (@OfNat.ofNat.{0} (@Nat) (98 : Nat) (@instOfNatNat (98 : Nat))))) (@PartACanonical.PrivateABI.a0014.{(0 + 1)} (fun (_v6
  : (@Option.{0} (@Bool))) =>
(@Nat)) _v3 (fun (_v6 : (@Unit)) =>
(@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (fun (_v6 : (@Unit)) =>
(@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (fun (_v6 : (@Unit)) =>
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
  (@Pnp3.Complexity.Uniform.V1.Move.stay) (@Pnp3.Complexity.Uniform.V1.Move.right))))))))))))) := by
  exact @CappedWorkspace.setup_row

-- Independent literal expected type for CarryReadyCompletion.check_raw.
noncomputable def PartACanonical.Types.p0274 :
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
  Nat) (@instOfNatNat (7 : Nat))))) (fun (_v30 : (@Not (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 _v16) _v12)
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v16)) _v12)
  (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))))) =>
(@PartACanonical.PrivateABI.a0015 _v0 _v1 _v2 _v6 _v7 _v30))) _v27)) (fun (_v30 : (@Fin
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
  (@instOfNatNat (1 : Nat)))) (@lt_of_le_of_lt.{0} (@Nat) (@Nat.instPreorder) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  _v14 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat)
  (@instOfNatNat (5 : Nat))) _v16)) _v12) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11)
  (@Decidable.byContradiction (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v14 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 (@HMul.hMul.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 :
  Nat))) _v16)) _v12) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))) (@Nat.decLe (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v14 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v16)) _v12) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))))
  (fun (_v30 : (@Not (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v14 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 (@HMul.hMul.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 :
  Nat))) _v16)) _v12) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))))) =>
(@PartACanonical.PrivateABI.a0016 _v0 _v1 _v2 _v6 _v7 _v30))) _v27)) (fun (_v30 : (@Fin
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
(@And (@CappedWeight.Target.Cap _v0 _v12 _v16 _v28 _v29 _v30 _v31 _v32) (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v9
  (@Cursor.Target.M _v0 _v12 _v7)) (@_v25 (@Cursor.Target.image _v18 _v0 _v9 _v12 _v7
  _v14)))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @CarryReadyCompletion.check_raw

-- Complete literal proposition for CarryReadyCompletion.check_raw; original proof reused.
theorem PartACanonical.Surface.m0175 :
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
  Nat) (@instOfNatNat (7 : Nat))))) (fun (_v30 : (@Not (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 _v16) _v12)
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v16)) _v12)
  (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))))) =>
(@PartACanonical.PrivateABI.a0015 _v0 _v1 _v2 _v6 _v7 _v30))) _v27)) (fun (_v30 : (@Fin
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
  (@instOfNatNat (1 : Nat)))) (@lt_of_le_of_lt.{0} (@Nat) (@Nat.instPreorder) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  _v14 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat)
  (@instOfNatNat (5 : Nat))) _v16)) _v12) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11)
  (@Decidable.byContradiction (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v14 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 (@HMul.hMul.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 :
  Nat))) _v16)) _v12) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))) (@Nat.decLe (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v14 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v16)) _v12) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))))
  (fun (_v30 : (@Not (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v14 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 (@HMul.hMul.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 :
  Nat))) _v16)) _v12) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))))) =>
(@PartACanonical.PrivateABI.a0016 _v0 _v1 _v2 _v6 _v7 _v30))) _v27)) (fun (_v30 : (@Fin
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
  exact @CarryReadyCompletion.check_raw

-- Independent literal expected type for CertificateGuardClosure.Audit.check_guard_equation.
noncomputable def PartACanonical.Types.p0296 :
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.UniformTM) (@CertificateGuardClosure.guard)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.mk (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat))) (@Fin.mk
  (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat))) (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 :
  Nat))) (@of_decide_eq_true (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (64 : Nat)
  (@instOfNatNat (64 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat)))) (@id.{0} (@Eq.{(0 + 1)}
  (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (64 : Nat)
  (@instOfNatNat (64 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat))))) (@Bool.true))
  (@Eq.refl.{(0 + 1)} (@Bool) (@Bool.true))))) (@Fin.mk (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (65 : Nat) (@instOfNatNat (65 : Nat))) (@of_decide_eq_true (@LT.lt.{0} (@Nat) (@instLTNat)
  (@OfNat.ofNat.{0} (@Nat) (65 : Nat) (@instOfNatNat (65 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 :
  Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (65 : Nat) (@instOfNatNat (65 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat)
  (@instOfNatNat (67 : Nat)))) (@id.{0} (@Eq.{(0 + 1)} (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat) (@instLTNat)
  (@OfNat.ofNat.{0} (@Nat) (65 : Nat) (@instOfNatNat (65 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 :
  Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (65 : Nat) (@instOfNatNat (65 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat)
  (@instOfNatNat (67 : Nat))))) (@Bool.true)) (@Eq.refl.{(0 + 1)} (@Bool) (@Bool.true))))) (@Fin.mk (@OfNat.ofNat.{0}
  (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat))) (@OfNat.ofNat.{0} (@Nat) (66 : Nat) (@instOfNatNat (66 : Nat)))
  (@of_decide_eq_true (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (66 : Nat) (@instOfNatNat (66 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (66 : Nat)
  (@instOfNatNat (66 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat)))) (@id.{0} (@Eq.{(0 + 1)}
  (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (66 : Nat) (@instOfNatNat (66 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (66 : Nat)
  (@instOfNatNat (66 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat))))) (@Bool.true))
  (@Eq.refl.{(0 + 1)} (@Bool) (@Bool.true))))) (@of_decide_eq_true (@Ne.{(0 + 1)} (@Fin (@OfNat.ofNat.{0} (@Nat) (67 :
  Nat) (@instOfNatNat (67 : Nat)))) (@Fin.mk (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (65 : Nat) (@instOfNatNat (65 : Nat))) (@of_decide_eq_true (@LT.lt.{0} (@Nat) (@instLTNat)
  (@OfNat.ofNat.{0} (@Nat) (65 : Nat) (@instOfNatNat (65 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 :
  Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (65 : Nat) (@instOfNatNat (65 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat)
  (@instOfNatNat (67 : Nat)))) (@id.{0} (@Eq.{(0 + 1)} (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat) (@instLTNat)
  (@OfNat.ofNat.{0} (@Nat) (65 : Nat) (@instOfNatNat (65 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 :
  Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (65 : Nat) (@instOfNatNat (65 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat)
  (@instOfNatNat (67 : Nat))))) (@Bool.true)) (@Eq.refl.{(0 + 1)} (@Bool) (@Bool.true))))) (@Fin.mk (@OfNat.ofNat.{0}
  (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat))) (@OfNat.ofNat.{0} (@Nat) (66 : Nat) (@instOfNatNat (66 : Nat)))
  (@of_decide_eq_true (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (66 : Nat) (@instOfNatNat (66 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (66 : Nat)
  (@instOfNatNat (66 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat)))) (@id.{0} (@Eq.{(0 + 1)}
  (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (66 : Nat) (@instOfNatNat (66 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (66 : Nat)
  (@instOfNatNat (66 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat))))) (@Bool.true))
  (@Eq.refl.{(0 + 1)} (@Bool) (@Bool.true)))))) (@instDecidableNot (@Eq.{(0 + 1)} (@Fin (@OfNat.ofNat.{0} (@Nat) (67 :
  Nat) (@instOfNatNat (67 : Nat)))) (@Fin.mk (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (65 : Nat) (@instOfNatNat (65 : Nat))) (@of_decide_eq_true (@LT.lt.{0} (@Nat) (@instLTNat)
  (@OfNat.ofNat.{0} (@Nat) (65 : Nat) (@instOfNatNat (65 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 :
  Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (65 : Nat) (@instOfNatNat (65 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat)
  (@instOfNatNat (67 : Nat)))) (@id.{0} (@Eq.{(0 + 1)} (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat) (@instLTNat)
  (@OfNat.ofNat.{0} (@Nat) (65 : Nat) (@instOfNatNat (65 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 :
  Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (65 : Nat) (@instOfNatNat (65 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat)
  (@instOfNatNat (67 : Nat))))) (@Bool.true)) (@Eq.refl.{(0 + 1)} (@Bool) (@Bool.true))))) (@Fin.mk (@OfNat.ofNat.{0}
  (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat))) (@OfNat.ofNat.{0} (@Nat) (66 : Nat) (@instOfNatNat (66 : Nat)))
  (@of_decide_eq_true (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (66 : Nat) (@instOfNatNat (66 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (66 : Nat)
  (@instOfNatNat (66 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat)))) (@id.{0} (@Eq.{(0 + 1)}
  (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (66 : Nat) (@instOfNatNat (66 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (66 : Nat)
  (@instOfNatNat (66 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat))))) (@Bool.true))
  (@Eq.refl.{(0 + 1)} (@Bool) (@Bool.true)))))) (@instDecidableEqFin (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat
  (67 : Nat))) (@Fin.mk (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat))) (@OfNat.ofNat.{0} (@Nat) (65 :
  Nat) (@instOfNatNat (65 : Nat))) (@of_decide_eq_true (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (65 : Nat)
  (@instOfNatNat (65 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat)))) (@Nat.decLt
  (@OfNat.ofNat.{0} (@Nat) (65 : Nat) (@instOfNatNat (65 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 :
  Nat)))) (@id.{0} (@Eq.{(0 + 1)} (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (65
  : Nat) (@instOfNatNat (65 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat)))) (@Nat.decLt
  (@OfNat.ofNat.{0} (@Nat) (65 : Nat) (@instOfNatNat (65 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 :
  Nat))))) (@Bool.true)) (@Eq.refl.{(0 + 1)} (@Bool) (@Bool.true))))) (@Fin.mk (@OfNat.ofNat.{0} (@Nat) (67 : Nat)
  (@instOfNatNat (67 : Nat))) (@OfNat.ofNat.{0} (@Nat) (66 : Nat) (@instOfNatNat (66 : Nat))) (@of_decide_eq_true
  (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (66 : Nat) (@instOfNatNat (66 : Nat))) (@OfNat.ofNat.{0} (@Nat)
  (67 : Nat) (@instOfNatNat (67 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (66 : Nat) (@instOfNatNat (66 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat)))) (@id.{0} (@Eq.{(0 + 1)} (@Bool) (@Decidable.decide
  (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (66 : Nat) (@instOfNatNat (66 : Nat))) (@OfNat.ofNat.{0} (@Nat)
  (67 : Nat) (@instOfNatNat (67 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (66 : Nat) (@instOfNatNat (66 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat))))) (@Bool.true)) (@Eq.refl.{(0 + 1)} (@Bool)
  (@Bool.true))))))) (@id.{0} (@Eq.{(0 + 1)} (@Bool) (@Decidable.decide (@Ne.{(0 + 1)} (@Fin (@OfNat.ofNat.{0} (@Nat) (67
  : Nat) (@instOfNatNat (67 : Nat)))) (@Fin.mk (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (65 : Nat) (@instOfNatNat (65 : Nat))) (@of_decide_eq_true (@LT.lt.{0} (@Nat) (@instLTNat)
  (@OfNat.ofNat.{0} (@Nat) (65 : Nat) (@instOfNatNat (65 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 :
  Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (65 : Nat) (@instOfNatNat (65 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat)
  (@instOfNatNat (67 : Nat)))) (@id.{0} (@Eq.{(0 + 1)} (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat) (@instLTNat)
  (@OfNat.ofNat.{0} (@Nat) (65 : Nat) (@instOfNatNat (65 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 :
  Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (65 : Nat) (@instOfNatNat (65 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat)
  (@instOfNatNat (67 : Nat))))) (@Bool.true)) (@Eq.refl.{(0 + 1)} (@Bool) (@Bool.true))))) (@Fin.mk (@OfNat.ofNat.{0}
  (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat))) (@OfNat.ofNat.{0} (@Nat) (66 : Nat) (@instOfNatNat (66 : Nat)))
  (@of_decide_eq_true (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (66 : Nat) (@instOfNatNat (66 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (66 : Nat)
  (@instOfNatNat (66 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat)))) (@id.{0} (@Eq.{(0 + 1)}
  (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (66 : Nat) (@instOfNatNat (66 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (66 : Nat)
  (@instOfNatNat (66 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat))))) (@Bool.true))
  (@Eq.refl.{(0 + 1)} (@Bool) (@Bool.true)))))) (@instDecidableNot (@Eq.{(0 + 1)} (@Fin (@OfNat.ofNat.{0} (@Nat) (67 :
  Nat) (@instOfNatNat (67 : Nat)))) (@Fin.mk (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (65 : Nat) (@instOfNatNat (65 : Nat))) (@of_decide_eq_true (@LT.lt.{0} (@Nat) (@instLTNat)
  (@OfNat.ofNat.{0} (@Nat) (65 : Nat) (@instOfNatNat (65 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 :
  Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (65 : Nat) (@instOfNatNat (65 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat)
  (@instOfNatNat (67 : Nat)))) (@id.{0} (@Eq.{(0 + 1)} (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat) (@instLTNat)
  (@OfNat.ofNat.{0} (@Nat) (65 : Nat) (@instOfNatNat (65 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 :
  Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (65 : Nat) (@instOfNatNat (65 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat)
  (@instOfNatNat (67 : Nat))))) (@Bool.true)) (@Eq.refl.{(0 + 1)} (@Bool) (@Bool.true))))) (@Fin.mk (@OfNat.ofNat.{0}
  (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat))) (@OfNat.ofNat.{0} (@Nat) (66 : Nat) (@instOfNatNat (66 : Nat)))
  (@of_decide_eq_true (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (66 : Nat) (@instOfNatNat (66 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (66 : Nat)
  (@instOfNatNat (66 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat)))) (@id.{0} (@Eq.{(0 + 1)}
  (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (66 : Nat) (@instOfNatNat (66 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (66 : Nat)
  (@instOfNatNat (66 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat))))) (@Bool.true))
  (@Eq.refl.{(0 + 1)} (@Bool) (@Bool.true)))))) (@instDecidableEqFin (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat
  (67 : Nat))) (@Fin.mk (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat))) (@OfNat.ofNat.{0} (@Nat) (65 :
  Nat) (@instOfNatNat (65 : Nat))) (@of_decide_eq_true (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (65 : Nat)
  (@instOfNatNat (65 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat)))) (@Nat.decLt
  (@OfNat.ofNat.{0} (@Nat) (65 : Nat) (@instOfNatNat (65 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 :
  Nat)))) (@id.{0} (@Eq.{(0 + 1)} (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (65
  : Nat) (@instOfNatNat (65 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat)))) (@Nat.decLt
  (@OfNat.ofNat.{0} (@Nat) (65 : Nat) (@instOfNatNat (65 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 :
  Nat))))) (@Bool.true)) (@Eq.refl.{(0 + 1)} (@Bool) (@Bool.true))))) (@Fin.mk (@OfNat.ofNat.{0} (@Nat) (67 : Nat)
  (@instOfNatNat (67 : Nat))) (@OfNat.ofNat.{0} (@Nat) (66 : Nat) (@instOfNatNat (66 : Nat))) (@of_decide_eq_true
  (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (66 : Nat) (@instOfNatNat (66 : Nat))) (@OfNat.ofNat.{0} (@Nat)
  (67 : Nat) (@instOfNatNat (67 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (66 : Nat) (@instOfNatNat (66 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat)))) (@id.{0} (@Eq.{(0 + 1)} (@Bool) (@Decidable.decide
  (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (66 : Nat) (@instOfNatNat (66 : Nat))) (@OfNat.ofNat.{0} (@Nat)
  (67 : Nat) (@instOfNatNat (67 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (66 : Nat) (@instOfNatNat (66 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat))))) (@Bool.true)) (@Eq.refl.{(0 + 1)} (@Bool)
  (@Bool.true)))))))) (@Bool.true)) (@Eq.refl.{(0 + 1)} (@Bool) (@Bool.true)))) (@PartACanonical.PrivateABI.a0019))) := by
  exact @CertificateGuardClosure.Audit.check_guard_equation

-- Complete literal proposition for CertificateGuardClosure.Audit.check_guard_equation; original proof reused.
theorem PartACanonical.Surface.m0189 :
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.UniformTM) (@CertificateGuardClosure.guard)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.mk (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat))) (@Fin.mk
  (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat))) (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 :
  Nat))) (@of_decide_eq_true (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (64 : Nat)
  (@instOfNatNat (64 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat)))) (@id.{0} (@Eq.{(0 + 1)}
  (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (64 : Nat)
  (@instOfNatNat (64 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat))))) (@Bool.true))
  (@Eq.refl.{(0 + 1)} (@Bool) (@Bool.true))))) (@Fin.mk (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (65 : Nat) (@instOfNatNat (65 : Nat))) (@of_decide_eq_true (@LT.lt.{0} (@Nat) (@instLTNat)
  (@OfNat.ofNat.{0} (@Nat) (65 : Nat) (@instOfNatNat (65 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 :
  Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (65 : Nat) (@instOfNatNat (65 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat)
  (@instOfNatNat (67 : Nat)))) (@id.{0} (@Eq.{(0 + 1)} (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat) (@instLTNat)
  (@OfNat.ofNat.{0} (@Nat) (65 : Nat) (@instOfNatNat (65 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 :
  Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (65 : Nat) (@instOfNatNat (65 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat)
  (@instOfNatNat (67 : Nat))))) (@Bool.true)) (@Eq.refl.{(0 + 1)} (@Bool) (@Bool.true))))) (@Fin.mk (@OfNat.ofNat.{0}
  (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat))) (@OfNat.ofNat.{0} (@Nat) (66 : Nat) (@instOfNatNat (66 : Nat)))
  (@of_decide_eq_true (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (66 : Nat) (@instOfNatNat (66 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (66 : Nat)
  (@instOfNatNat (66 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat)))) (@id.{0} (@Eq.{(0 + 1)}
  (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (66 : Nat) (@instOfNatNat (66 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (66 : Nat)
  (@instOfNatNat (66 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat))))) (@Bool.true))
  (@Eq.refl.{(0 + 1)} (@Bool) (@Bool.true))))) (@of_decide_eq_true (@Ne.{(0 + 1)} (@Fin (@OfNat.ofNat.{0} (@Nat) (67 :
  Nat) (@instOfNatNat (67 : Nat)))) (@Fin.mk (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (65 : Nat) (@instOfNatNat (65 : Nat))) (@of_decide_eq_true (@LT.lt.{0} (@Nat) (@instLTNat)
  (@OfNat.ofNat.{0} (@Nat) (65 : Nat) (@instOfNatNat (65 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 :
  Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (65 : Nat) (@instOfNatNat (65 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat)
  (@instOfNatNat (67 : Nat)))) (@id.{0} (@Eq.{(0 + 1)} (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat) (@instLTNat)
  (@OfNat.ofNat.{0} (@Nat) (65 : Nat) (@instOfNatNat (65 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 :
  Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (65 : Nat) (@instOfNatNat (65 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat)
  (@instOfNatNat (67 : Nat))))) (@Bool.true)) (@Eq.refl.{(0 + 1)} (@Bool) (@Bool.true))))) (@Fin.mk (@OfNat.ofNat.{0}
  (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat))) (@OfNat.ofNat.{0} (@Nat) (66 : Nat) (@instOfNatNat (66 : Nat)))
  (@of_decide_eq_true (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (66 : Nat) (@instOfNatNat (66 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (66 : Nat)
  (@instOfNatNat (66 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat)))) (@id.{0} (@Eq.{(0 + 1)}
  (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (66 : Nat) (@instOfNatNat (66 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (66 : Nat)
  (@instOfNatNat (66 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat))))) (@Bool.true))
  (@Eq.refl.{(0 + 1)} (@Bool) (@Bool.true)))))) (@instDecidableNot (@Eq.{(0 + 1)} (@Fin (@OfNat.ofNat.{0} (@Nat) (67 :
  Nat) (@instOfNatNat (67 : Nat)))) (@Fin.mk (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (65 : Nat) (@instOfNatNat (65 : Nat))) (@of_decide_eq_true (@LT.lt.{0} (@Nat) (@instLTNat)
  (@OfNat.ofNat.{0} (@Nat) (65 : Nat) (@instOfNatNat (65 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 :
  Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (65 : Nat) (@instOfNatNat (65 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat)
  (@instOfNatNat (67 : Nat)))) (@id.{0} (@Eq.{(0 + 1)} (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat) (@instLTNat)
  (@OfNat.ofNat.{0} (@Nat) (65 : Nat) (@instOfNatNat (65 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 :
  Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (65 : Nat) (@instOfNatNat (65 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat)
  (@instOfNatNat (67 : Nat))))) (@Bool.true)) (@Eq.refl.{(0 + 1)} (@Bool) (@Bool.true))))) (@Fin.mk (@OfNat.ofNat.{0}
  (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat))) (@OfNat.ofNat.{0} (@Nat) (66 : Nat) (@instOfNatNat (66 : Nat)))
  (@of_decide_eq_true (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (66 : Nat) (@instOfNatNat (66 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (66 : Nat)
  (@instOfNatNat (66 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat)))) (@id.{0} (@Eq.{(0 + 1)}
  (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (66 : Nat) (@instOfNatNat (66 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (66 : Nat)
  (@instOfNatNat (66 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat))))) (@Bool.true))
  (@Eq.refl.{(0 + 1)} (@Bool) (@Bool.true)))))) (@instDecidableEqFin (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat
  (67 : Nat))) (@Fin.mk (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat))) (@OfNat.ofNat.{0} (@Nat) (65 :
  Nat) (@instOfNatNat (65 : Nat))) (@of_decide_eq_true (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (65 : Nat)
  (@instOfNatNat (65 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat)))) (@Nat.decLt
  (@OfNat.ofNat.{0} (@Nat) (65 : Nat) (@instOfNatNat (65 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 :
  Nat)))) (@id.{0} (@Eq.{(0 + 1)} (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (65
  : Nat) (@instOfNatNat (65 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat)))) (@Nat.decLt
  (@OfNat.ofNat.{0} (@Nat) (65 : Nat) (@instOfNatNat (65 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 :
  Nat))))) (@Bool.true)) (@Eq.refl.{(0 + 1)} (@Bool) (@Bool.true))))) (@Fin.mk (@OfNat.ofNat.{0} (@Nat) (67 : Nat)
  (@instOfNatNat (67 : Nat))) (@OfNat.ofNat.{0} (@Nat) (66 : Nat) (@instOfNatNat (66 : Nat))) (@of_decide_eq_true
  (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (66 : Nat) (@instOfNatNat (66 : Nat))) (@OfNat.ofNat.{0} (@Nat)
  (67 : Nat) (@instOfNatNat (67 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (66 : Nat) (@instOfNatNat (66 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat)))) (@id.{0} (@Eq.{(0 + 1)} (@Bool) (@Decidable.decide
  (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (66 : Nat) (@instOfNatNat (66 : Nat))) (@OfNat.ofNat.{0} (@Nat)
  (67 : Nat) (@instOfNatNat (67 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (66 : Nat) (@instOfNatNat (66 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat))))) (@Bool.true)) (@Eq.refl.{(0 + 1)} (@Bool)
  (@Bool.true))))))) (@id.{0} (@Eq.{(0 + 1)} (@Bool) (@Decidable.decide (@Ne.{(0 + 1)} (@Fin (@OfNat.ofNat.{0} (@Nat) (67
  : Nat) (@instOfNatNat (67 : Nat)))) (@Fin.mk (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (65 : Nat) (@instOfNatNat (65 : Nat))) (@of_decide_eq_true (@LT.lt.{0} (@Nat) (@instLTNat)
  (@OfNat.ofNat.{0} (@Nat) (65 : Nat) (@instOfNatNat (65 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 :
  Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (65 : Nat) (@instOfNatNat (65 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat)
  (@instOfNatNat (67 : Nat)))) (@id.{0} (@Eq.{(0 + 1)} (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat) (@instLTNat)
  (@OfNat.ofNat.{0} (@Nat) (65 : Nat) (@instOfNatNat (65 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 :
  Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (65 : Nat) (@instOfNatNat (65 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat)
  (@instOfNatNat (67 : Nat))))) (@Bool.true)) (@Eq.refl.{(0 + 1)} (@Bool) (@Bool.true))))) (@Fin.mk (@OfNat.ofNat.{0}
  (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat))) (@OfNat.ofNat.{0} (@Nat) (66 : Nat) (@instOfNatNat (66 : Nat)))
  (@of_decide_eq_true (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (66 : Nat) (@instOfNatNat (66 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (66 : Nat)
  (@instOfNatNat (66 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat)))) (@id.{0} (@Eq.{(0 + 1)}
  (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (66 : Nat) (@instOfNatNat (66 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (66 : Nat)
  (@instOfNatNat (66 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat))))) (@Bool.true))
  (@Eq.refl.{(0 + 1)} (@Bool) (@Bool.true)))))) (@instDecidableNot (@Eq.{(0 + 1)} (@Fin (@OfNat.ofNat.{0} (@Nat) (67 :
  Nat) (@instOfNatNat (67 : Nat)))) (@Fin.mk (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (65 : Nat) (@instOfNatNat (65 : Nat))) (@of_decide_eq_true (@LT.lt.{0} (@Nat) (@instLTNat)
  (@OfNat.ofNat.{0} (@Nat) (65 : Nat) (@instOfNatNat (65 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 :
  Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (65 : Nat) (@instOfNatNat (65 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat)
  (@instOfNatNat (67 : Nat)))) (@id.{0} (@Eq.{(0 + 1)} (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat) (@instLTNat)
  (@OfNat.ofNat.{0} (@Nat) (65 : Nat) (@instOfNatNat (65 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 :
  Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (65 : Nat) (@instOfNatNat (65 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat)
  (@instOfNatNat (67 : Nat))))) (@Bool.true)) (@Eq.refl.{(0 + 1)} (@Bool) (@Bool.true))))) (@Fin.mk (@OfNat.ofNat.{0}
  (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat))) (@OfNat.ofNat.{0} (@Nat) (66 : Nat) (@instOfNatNat (66 : Nat)))
  (@of_decide_eq_true (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (66 : Nat) (@instOfNatNat (66 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (66 : Nat)
  (@instOfNatNat (66 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat)))) (@id.{0} (@Eq.{(0 + 1)}
  (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (66 : Nat) (@instOfNatNat (66 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (66 : Nat)
  (@instOfNatNat (66 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat))))) (@Bool.true))
  (@Eq.refl.{(0 + 1)} (@Bool) (@Bool.true)))))) (@instDecidableEqFin (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat
  (67 : Nat))) (@Fin.mk (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat))) (@OfNat.ofNat.{0} (@Nat) (65 :
  Nat) (@instOfNatNat (65 : Nat))) (@of_decide_eq_true (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (65 : Nat)
  (@instOfNatNat (65 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat)))) (@Nat.decLt
  (@OfNat.ofNat.{0} (@Nat) (65 : Nat) (@instOfNatNat (65 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 :
  Nat)))) (@id.{0} (@Eq.{(0 + 1)} (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (65
  : Nat) (@instOfNatNat (65 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat)))) (@Nat.decLt
  (@OfNat.ofNat.{0} (@Nat) (65 : Nat) (@instOfNatNat (65 : Nat))) (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 :
  Nat))))) (@Bool.true)) (@Eq.refl.{(0 + 1)} (@Bool) (@Bool.true))))) (@Fin.mk (@OfNat.ofNat.{0} (@Nat) (67 : Nat)
  (@instOfNatNat (67 : Nat))) (@OfNat.ofNat.{0} (@Nat) (66 : Nat) (@instOfNatNat (66 : Nat))) (@of_decide_eq_true
  (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (66 : Nat) (@instOfNatNat (66 : Nat))) (@OfNat.ofNat.{0} (@Nat)
  (67 : Nat) (@instOfNatNat (67 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (66 : Nat) (@instOfNatNat (66 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat)))) (@id.{0} (@Eq.{(0 + 1)} (@Bool) (@Decidable.decide
  (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (66 : Nat) (@instOfNatNat (66 : Nat))) (@OfNat.ofNat.{0} (@Nat)
  (67 : Nat) (@instOfNatNat (67 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (66 : Nat) (@instOfNatNat (66 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat))))) (@Bool.true)) (@Eq.refl.{(0 + 1)} (@Bool)
  (@Bool.true)))))))) (@Bool.true)) (@Eq.refl.{(0 + 1)} (@Bool) (@Bool.true)))) (@PartACanonical.PrivateABI.a0019))) := by
  exact @CertificateGuardClosure.Audit.check_guard_equation

-- Independent literal expected type for CertificateGuardClosure.guard.eq_1.
noncomputable def PartACanonical.Types.p0308 :
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.UniformTM) (@CertificateGuardClosure.guard)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.mk (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat))) (@Fin.mk
  (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat))) (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 :
  Nat))) (@CertificateGuardClosure.guard._proof_1)) (@PartACanonical.PrivateABI.a0017) (@PartACanonical.PrivateABI.a0018)
  (@CertificateGuardClosure.guard._proof_2) (@PartACanonical.PrivateABI.a0019))) := by
  exact @CertificateGuardClosure.guard.eq_1

-- Complete literal proposition for CertificateGuardClosure.guard.eq_1; original proof reused.
theorem PartACanonical.Surface.m0195 :
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.UniformTM) (@CertificateGuardClosure.guard)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.mk (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat))) (@Fin.mk
  (@OfNat.ofNat.{0} (@Nat) (67 : Nat) (@instOfNatNat (67 : Nat))) (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 :
  Nat))) (@CertificateGuardClosure.guard._proof_1)) (@PartACanonical.PrivateABI.a0017) (@PartACanonical.PrivateABI.a0018)
  (@CertificateGuardClosure.guard._proof_2) (@PartACanonical.PrivateABI.a0019))) := by
  exact @CertificateGuardClosure.guard.eq_1

-- Independent literal expected type for Cursor.machine.eq_1.
noncomputable def PartACanonical.Types.p0331 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.UniformTM) (@Cursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.UniformTM.mk
  (@Cursor.stateCount _v0) (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Cursor.q _v0
  (@OfNat.ofNat.{0} (@Nat) (39 : Nat) (@instOfNatNat (39 : Nat)))) (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (40 : Nat)
  (@instOfNatNat (40 : Nat)))) (@Cursor.machine._proof_3 _v0) (@PartACanonical.PrivateABI.a0020 _v0
  (@PartACanonical.PrivateABI.a0021 _v0))))) := by
  exact @Cursor.machine.eq_1

-- Complete literal proposition for Cursor.machine.eq_1; original proof reused.
theorem PartACanonical.Surface.m0205 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.UniformTM) (@Cursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.UniformTM.mk
  (@Cursor.stateCount _v0) (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Cursor.q _v0
  (@OfNat.ofNat.{0} (@Nat) (39 : Nat) (@instOfNatNat (39 : Nat)))) (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (40 : Nat)
  (@instOfNatNat (40 : Nat)))) (@Cursor.machine._proof_3 _v0) (@PartACanonical.PrivateABI.a0020 _v0
  (@PartACanonical.PrivateABI.a0021 _v0))))) := by
  exact @Cursor.machine.eq_1

-- Independent literal expected type for Cursor.rows.eq_1.
noncomputable def PartACanonical.Types.p0345 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (∀ (_v1 : (@Fin (@Cursor.stateCount _v0))),
(∀ (_v2 : (@Option.{0} (@Bool))),
(@Prod.{0, 0} (@Fin (@Cursor.stateCount _v0)) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)))))
  (@Cursor.rows _v0) (@PartACanonical.PrivateABI.a0020 _v0 (@PartACanonical.PrivateABI.a0021 _v0)))) := by
  exact @Cursor.rows.eq_1

-- Complete literal proposition for Cursor.rows.eq_1; original proof reused.
theorem PartACanonical.Surface.m0215 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (∀ (_v1 : (@Fin (@Cursor.stateCount _v0))),
(∀ (_v2 : (@Option.{0} (@Bool))),
(@Prod.{0, 0} (@Fin (@Cursor.stateCount _v0)) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)))))
  (@Cursor.rows _v0) (@PartACanonical.PrivateABI.a0020 _v0 (@PartACanonical.PrivateABI.a0021 _v0)))) := by
  exact @Cursor.rows.eq_1

-- Independent literal expected type for FullFinalClosure.full_endpoint_full.
noncomputable def PartACanonical.Types.p0373 :
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
  exact @FullFinalClosure.full_endpoint_full

-- Complete literal proposition for FullFinalClosure.full_endpoint_full; original proof reused.
theorem PartACanonical.Surface.m0229 :
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
  exact @FullFinalClosure.full_endpoint_full

-- Independent literal expected type for FullFinalClosure.machine.
noncomputable def PartACanonical.Types.p0375 :
(∀ (_v0 : (@Nat)),
(@Pnp3.Complexity.Uniform.V1.UniformTM)) := by
  exact @FullFinalClosure.machine

-- Independent literal expected type for FullIngressClosure.check_clone_sum.
noncomputable def PartACanonical.Types.p0388 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v2 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))))))))))))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))) _v0) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2
  : Nat) (@instOfNatNat (2 : Nat))) _v2)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v1)) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8
  : Nat)))))))) := by
  exact @FullIngressClosure.check_clone_sum

-- Complete literal proposition for FullIngressClosure.check_clone_sum; original proof reused.
theorem PartACanonical.Surface.m0238 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v2 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))))))))))))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))) _v0) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2
  : Nat) (@instOfNatNat (2 : Nat))) _v2)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v1)) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8
  : Nat)))))))) := by
  exact @FullIngressClosure.check_clone_sum

-- Independent literal expected type for FullIngressClosure.check_discrete_span.
noncomputable def PartACanonical.Types.p0389 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Nat))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@LE.le.{0} (@Nat) (@instLENat) _v1 _v2)),
(∀ (_v4 : (∀ (_v4 : (@Nat)),
(∀ (_v5 : (@LE.le.{0} (@Nat) (@instLENat) _v1 _v4)),
(∀ (_v6 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 _v2)),
(@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 _v4) (@_v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v4 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))))))),
(@LE.le.{0} (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v2 _v1)
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@_v0 _v2) (@_v0 _v1)))))))) := by
  exact @FullIngressClosure.check_discrete_span

-- Complete literal proposition for FullIngressClosure.check_discrete_span; original proof reused.
theorem PartACanonical.Surface.m0239 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Nat))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@LE.le.{0} (@Nat) (@instLENat) _v1 _v2)),
(∀ (_v4 : (∀ (_v4 : (@Nat)),
(∀ (_v5 : (@LE.le.{0} (@Nat) (@instLENat) _v1 _v4)),
(∀ (_v6 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 _v2)),
(@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 _v4) (@_v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v4 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))))))),
(@LE.le.{0} (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v2 _v1)
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@_v0 _v2) (@_v0 _v1)))))))) := by
  exact @FullIngressClosure.check_discrete_span

-- Independent literal expected type for FullIngressClosure.clone_sum.
noncomputable def PartACanonical.Types.p0391 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v2 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))))))))))))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))) _v0) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2
  : Nat) (@instOfNatNat (2 : Nat))) _v2)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v1)) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8
  : Nat)))))))) := by
  exact @FullIngressClosure.clone_sum

-- Complete literal proposition for FullIngressClosure.clone_sum; original proof reused.
theorem PartACanonical.Surface.m0241 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v2 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))))))))))))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))) _v0) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2
  : Nat) (@instOfNatNat (2 : Nat))) _v2)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v1)) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8
  : Nat)))))))) := by
  exact @FullIngressClosure.clone_sum

-- Independent literal expected type for FullIngressClosure.discrete_span.
noncomputable def PartACanonical.Types.p0392 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Nat))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@LE.le.{0} (@Nat) (@instLENat) _v1 _v2)),
(∀ (_v4 : (∀ (_v4 : (@Nat)),
(∀ (_v5 : (@LE.le.{0} (@Nat) (@instLENat) _v1 _v4)),
(∀ (_v6 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 _v2)),
(@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 _v4) (@_v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v4 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))))))),
(@LE.le.{0} (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v2 _v1)
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@_v0 _v2) (@_v0 _v1)))))))) := by
  exact @FullIngressClosure.discrete_span

-- Complete literal proposition for FullIngressClosure.discrete_span; original proof reused.
theorem PartACanonical.Surface.m0242 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Nat))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@LE.le.{0} (@Nat) (@instLENat) _v1 _v2)),
(∀ (_v4 : (∀ (_v4 : (@Nat)),
(∀ (_v5 : (@LE.le.{0} (@Nat) (@instLENat) _v1 _v4)),
(∀ (_v6 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 _v2)),
(@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 _v4) (@_v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v4 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))))))),
(@LE.le.{0} (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v2 _v1)
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@_v0 _v2) (@_v0 _v1)))))))) := by
  exact @FullIngressClosure.discrete_span

-- Independent literal expected type for RuntimeBitLength.phase_row.
noncomputable def PartACanonical.Types.p0644 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Option.{0} (@Bool))),
(∀ (_v4 : (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (201 : Nat) (@instOfNatNat (201 : Nat))) _v1)),
(∀ (_v5 : (@LT.lt.{0} (@Nat) (@instLTNat) _v1 (@OfNat.ofNat.{0} (@Nat) (250 : Nat) (@instOfNatNat (250 : Nat))))),
(∀ (_v6 : (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@GetElem?.getElem?.{0, 0, 0} (@List.{0} (@Nat)) (@Nat) (@Nat) (fun (_v6 :
  (@List.{0} (@Nat))) =>
(fun (_v7 : (@Nat)) =>
(@LT.lt.{0} (@Nat) (@instLTNat) _v7 (@List.length.{0} (@Nat) _v6)))) (@List.instGetElem?NatLtLength.{0} (@Nat))
  (@RuntimeBitLength.instructions) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v1
  (@OfNat.ofNat.{0} (@Nat) (201 : Nat) (@instOfNatNat (201 : Nat))))) (@PartACanonical.PrivateABI.a0029.{(0 + 1)} (fun
  (_v6 : (@Option.{0} (@Bool))) =>
(@Nat)) _v3 (fun (_v6 : (@Unit)) =>
(@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (fun (_v6 : (@Unit)) =>
(@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (fun (_v6 : (@Unit)) =>
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
  (@Pnp3.Complexity.Uniform.V1.Move.stay) (@Pnp3.Complexity.Uniform.V1.Move.right))))))))))))) := by
  exact @RuntimeBitLength.phase_row

-- Complete literal proposition for RuntimeBitLength.phase_row; original proof reused.
theorem PartACanonical.Surface.m0384 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Option.{0} (@Bool))),
(∀ (_v4 : (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (201 : Nat) (@instOfNatNat (201 : Nat))) _v1)),
(∀ (_v5 : (@LT.lt.{0} (@Nat) (@instLTNat) _v1 (@OfNat.ofNat.{0} (@Nat) (250 : Nat) (@instOfNatNat (250 : Nat))))),
(∀ (_v6 : (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@GetElem?.getElem?.{0, 0, 0} (@List.{0} (@Nat)) (@Nat) (@Nat) (fun (_v6 :
  (@List.{0} (@Nat))) =>
(fun (_v7 : (@Nat)) =>
(@LT.lt.{0} (@Nat) (@instLTNat) _v7 (@List.length.{0} (@Nat) _v6)))) (@List.instGetElem?NatLtLength.{0} (@Nat))
  (@RuntimeBitLength.instructions) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v1
  (@OfNat.ofNat.{0} (@Nat) (201 : Nat) (@instOfNatNat (201 : Nat))))) (@PartACanonical.PrivateABI.a0029.{(0 + 1)} (fun
  (_v6 : (@Option.{0} (@Bool))) =>
(@Nat)) _v3 (fun (_v6 : (@Unit)) =>
(@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (fun (_v6 : (@Unit)) =>
(@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (fun (_v6 : (@Unit)) =>
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
  (@Pnp3.Complexity.Uniform.V1.Move.stay) (@Pnp3.Complexity.Uniform.V1.Move.right))))))))))))) := by
  exact @RuntimeBitLength.phase_row

-- Independent literal expected type for SerializedBodyCompletion.zero_quota_body.
noncomputable def PartACanonical.Types.p0684 :
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
(@PartACanonical.PrivateABI.a0030.{(0 + 1)} _v3 (fun (_v37 : (@Prod.{0, 0} (@Pnp3.Models.Circuit _v3) (@List.{0}
  (@Bool)))) =>
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
  (@Bool.true))))))) (@SerializedBodyCompletion.zero_quota_body.match_1.{(0 + 1)} (fun (_v38 : (@Option.{0} (@Prod.{0, 0}
  (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool))))) =>
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
  exact @SerializedBodyCompletion.zero_quota_body

-- Complete literal proposition for SerializedBodyCompletion.zero_quota_body; original proof reused.
theorem PartACanonical.Surface.m0414 :
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
(@PartACanonical.PrivateABI.a0030.{(0 + 1)} _v3 (fun (_v37 : (@Prod.{0, 0} (@Pnp3.Models.Circuit _v3) (@List.{0}
  (@Bool)))) =>
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
  (@Bool.true))))))) (@SerializedBodyCompletion.zero_quota_body.match_1.{(0 + 1)} (fun (_v38 : (@Option.{0} (@Prod.{0, 0}
  (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool))))) =>
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
  exact @SerializedBodyCompletion.zero_quota_body

-- Independent literal expected type for SerializedBodyCompletion.zero_window_body.
noncomputable def PartACanonical.Types.p0688 :
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
(@PartACanonical.PrivateABI.a0030.{(0 + 1)} _v3 (fun (_v37 : (@Prod.{0, 0} (@Pnp3.Models.Circuit _v3) (@List.{0}
  (@Bool)))) =>
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
  (@Bool.true))))))) (@SerializedBodyCompletion.zero_quota_body.match_1.{(0 + 1)} (fun (_v38 : (@Option.{0} (@Prod.{0, 0}
  (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool))))) =>
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
  exact @SerializedBodyCompletion.zero_window_body

-- Complete literal proposition for SerializedBodyCompletion.zero_window_body; original proof reused.
theorem PartACanonical.Surface.m0418 :
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
(@PartACanonical.PrivateABI.a0030.{(0 + 1)} _v3 (fun (_v37 : (@Prod.{0, 0} (@Pnp3.Models.Circuit _v3) (@List.{0}
  (@Bool)))) =>
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
  (@Bool.true))))))) (@SerializedBodyCompletion.zero_quota_body.match_1.{(0 + 1)} (fun (_v38 : (@Option.{0} (@Prod.{0, 0}
  (@Prod.{0, 0} (@Nat) (@Bool)) (@List.{0} (@Bool))))) =>
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
  exact @SerializedBodyCompletion.zero_window_body

-- Independent literal expected type for SmallIngress.Audit.check_raw_gamma_start.
noncomputable def PartACanonical.Types.p0705 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ (_v2 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v0)),
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v4 : (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.tagMatches (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1) (@Fin.append.{(0 + 1)} _v0 _v1 (@Bool) _v2 _v3))
  (@Bool.true))),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SmallIngress.producer)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SmallIngress.producer)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.installClock
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1))
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.contentClock _v0 _v1)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1))) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat
  (7 : Nat)))) (@Pnp3.Complexity.Uniform.V1.initialConfig (@SmallIngress.producer)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v0 _v1 _v2 _v3))) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SmallIngress.producer))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1)) (@SmallIngress.q (@OfNat.ofNat.{0} (@Nat) (124 : Nat) (@instOfNatNat (124 : Nat)))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (let _v5 : (@LE.le.{0} (@Nat) (@instLENat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  _v0 _v1))) := (@And.left (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1))) (@LE.le.{0} (@Nat) (@instLENat) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.installClock
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1))
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1))) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.resource_bounds
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)));
(let _v6 : (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1)) := (@And.right (@Eq.{(0 + 1)} (@Nat)
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1))
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.deadline _v0 _v1)) (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0}
  (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 _v1)) (@And.right (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat)))
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1))
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.startConfig _v0 _v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat))) _v2 _v3))) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine))) (@And (@Eq.{(0 + 1)} (@Nat)
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1))
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.deadline _v0 _v1)) (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0}
  (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 _v1))) (@And.right (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat)))
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1))
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.startConfig _v0 _v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat))) _v2 _v3)) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.finalConfig _v0 _v1 (@OfNat.ofNat.{0} (@Nat) (0 :
  Nat) (@instOfNatNat (0 : Nat))) _v2 _v3)) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat)))
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1))
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.startConfig _v0 _v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat))) _v2 _v3))) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine))) (@And (@Eq.{(0 + 1)} (@Nat)
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1))
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.deadline _v0 _v1)) (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0}
  (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 _v1)))) (@And.right (∀ (_v6 : (@Nat)),
(∀ (_v7 : (@LT.lt.{0} (@Nat) (@instLTNat) _v6
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1)))),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) _v6 (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.startConfig _v0 _v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) _v2 _v3))) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v6
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.startConfig _v0 _v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat))) _v2 _v3))) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine)))))) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat)))
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1))
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.startConfig _v0 _v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat))) _v2 _v3)) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.finalConfig _v0 _v1 (@OfNat.ofNat.{0} (@Nat) (0 :
  Nat) (@instOfNatNat (0 : Nat))) _v2 _v3)) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat)))
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1))
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.startConfig _v0 _v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat))) _v2 _v3))) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine))) (@And (@Eq.{(0 + 1)} (@Nat)
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1))
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.deadline _v0 _v1)) (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0}
  (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 _v1)))))
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.gate_first_arrival
  _v0 _v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v2 _v3 _v4)))));
(@id.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1)))) (@Decidable.byContradiction (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8
  : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v0) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))) _v0) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v1))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v0)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))) _v0) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v1))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (fun (_v7 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (8 : Nat)
  (@instOfNatNat (8 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v0) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))) _v0) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v1))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))))) =>
(@PartACanonical.PrivateABI.a0040 _v0 _v1 _v5 _v6 _v7)))))))
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencedContentTape _v0 _v1
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1)) _v2 _v3)))))))) := by
  exact @SmallIngress.Audit.check_raw_gamma_start

-- Complete literal proposition for SmallIngress.Audit.check_raw_gamma_start; original proof reused.
theorem PartACanonical.Surface.m0431 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ (_v2 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v0)),
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v4 : (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.tagMatches (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1) (@Fin.append.{(0 + 1)} _v0 _v1 (@Bool) _v2 _v3))
  (@Bool.true))),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SmallIngress.producer)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SmallIngress.producer)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.installClock
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1))
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.contentClock _v0 _v1)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1))) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat
  (7 : Nat)))) (@Pnp3.Complexity.Uniform.V1.initialConfig (@SmallIngress.producer)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v0 _v1 _v2 _v3))) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SmallIngress.producer))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1)) (@SmallIngress.q (@OfNat.ofNat.{0} (@Nat) (124 : Nat) (@instOfNatNat (124 : Nat)))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (let _v5 : (@LE.le.{0} (@Nat) (@instLENat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  _v0 _v1))) := (@And.left (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1))) (@LE.le.{0} (@Nat) (@instLENat) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.installClock
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1))
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1))) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.resource_bounds
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)));
(let _v6 : (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1)) := (@And.right (@Eq.{(0 + 1)} (@Nat)
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1))
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.deadline _v0 _v1)) (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0}
  (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 _v1)) (@And.right (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat)))
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1))
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.startConfig _v0 _v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat))) _v2 _v3))) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine))) (@And (@Eq.{(0 + 1)} (@Nat)
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1))
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.deadline _v0 _v1)) (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0}
  (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 _v1))) (@And.right (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat)))
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1))
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.startConfig _v0 _v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat))) _v2 _v3)) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.finalConfig _v0 _v1 (@OfNat.ofNat.{0} (@Nat) (0 :
  Nat) (@instOfNatNat (0 : Nat))) _v2 _v3)) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat)))
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1))
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.startConfig _v0 _v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat))) _v2 _v3))) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine))) (@And (@Eq.{(0 + 1)} (@Nat)
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1))
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.deadline _v0 _v1)) (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0}
  (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 _v1)))) (@And.right (∀ (_v6 : (@Nat)),
(∀ (_v7 : (@LT.lt.{0} (@Nat) (@instLTNat) _v6
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1)))),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) _v6 (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.startConfig _v0 _v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) _v2 _v3))) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v6
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.startConfig _v0 _v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat))) _v2 _v3))) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine)))))) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat)))
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1))
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.startConfig _v0 _v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat))) _v2 _v3)) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.finalConfig _v0 _v1 (@OfNat.ofNat.{0} (@Nat) (0 :
  Nat) (@instOfNatNat (0 : Nat))) _v2 _v3)) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat)))
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1))
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.startConfig _v0 _v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat))) _v2 _v3))) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine))) (@And (@Eq.{(0 + 1)} (@Nat)
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1))
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.deadline _v0 _v1)) (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0}
  (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 _v1)))))
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.gate_first_arrival
  _v0 _v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v2 _v3 _v4)))));
(@id.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1)))) (@Decidable.byContradiction (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8
  : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v0) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))) _v0) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v1))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v0)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))) _v0) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v1))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (fun (_v7 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (8 : Nat)
  (@instOfNatNat (8 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v0) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))) _v0) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v1))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))))) =>
(@PartACanonical.PrivateABI.a0040 _v0 _v1 _v5 _v6 _v7)))))))
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencedContentTape _v0 _v1
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1)) _v2 _v3)))))))) := by
  exact @SmallIngress.Audit.check_raw_gamma_start

-- Independent literal expected type for SmallIngress.liftOld.
noncomputable def PartACanonical.Types.p0718 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ (_v2 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PartACanonical.PrivateABI.a0034)) _v0 _v1)),
(@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SmallIngress.producer)) _v0
  _v1)))) := by
  exact @SmallIngress.liftOld

-- Independent literal expected type for SmallIngress.preserves_nonreject.
noncomputable def PartACanonical.Types.p0722 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ (_v2 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PartACanonical.PrivateABI.a0034)) _v0 _v1)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PartACanonical.PrivateABI.a0034)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PartACanonical.PrivateABI.a0034)) _v0 _v1 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PartACanonical.PrivateABI.a0034) _v0 _v1 _v3 _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject
  (@PartACanonical.PrivateABI.a0034)))),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SmallIngress.producer)) _v0 _v1) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SmallIngress.producer) _v0 _v1 _v3
  (@SmallIngress.liftOld _v0 _v1 _v2)) (@SmallIngress.liftOld _v0 _v1 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PartACanonical.PrivateABI.a0034) _v0 _v1 _v3 _v2)))))))) := by
  exact @SmallIngress.preserves_nonreject

-- Complete literal proposition for SmallIngress.preserves_nonreject; original proof reused.
theorem PartACanonical.Surface.m0436 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ (_v2 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PartACanonical.PrivateABI.a0034)) _v0 _v1)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@PartACanonical.PrivateABI.a0034)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@PartACanonical.PrivateABI.a0034)) _v0 _v1 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PartACanonical.PrivateABI.a0034) _v0 _v1 _v3 _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject
  (@PartACanonical.PrivateABI.a0034)))),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SmallIngress.producer)) _v0 _v1) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SmallIngress.producer) _v0 _v1 _v3
  (@SmallIngress.liftOld _v0 _v1 _v2)) (@SmallIngress.liftOld _v0 _v1 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@PartACanonical.PrivateABI.a0034) _v0 _v1 _v3 _v2)))))))) := by
  exact @SmallIngress.preserves_nonreject

-- Independent literal expected type for SmallIngress.raw_gamma_start.
noncomputable def PartACanonical.Types.p0726 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ (_v2 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v0)),
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v4 : (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.tagMatches (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1) (@Fin.append.{(0 + 1)} _v0 _v1 (@Bool) _v2 _v3))
  (@Bool.true))),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SmallIngress.producer)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SmallIngress.producer)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.installClock
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1))
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.contentClock _v0 _v1)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1))) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat
  (7 : Nat)))) (@Pnp3.Complexity.Uniform.V1.initialConfig (@SmallIngress.producer)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v0 _v1 _v2 _v3))) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SmallIngress.producer))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1)) (@SmallIngress.q (@OfNat.ofNat.{0} (@Nat) (124 : Nat) (@instOfNatNat (124 : Nat)))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (let _v5 : (@LE.le.{0} (@Nat) (@instLENat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  _v0 _v1))) := (@And.left (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1))) (@LE.le.{0} (@Nat) (@instLENat) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.installClock
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1))
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1))) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.resource_bounds
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)));
(let _v6 : (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1)) := (@And.right (@Eq.{(0 + 1)} (@Nat)
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1))
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.deadline _v0 _v1)) (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0}
  (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 _v1)) (@And.right (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat)))
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1))
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.startConfig _v0 _v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat))) _v2 _v3))) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine))) (@And (@Eq.{(0 + 1)} (@Nat)
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1))
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.deadline _v0 _v1)) (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0}
  (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 _v1))) (@And.right (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat)))
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1))
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.startConfig _v0 _v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat))) _v2 _v3)) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.finalConfig _v0 _v1 (@OfNat.ofNat.{0} (@Nat) (0 :
  Nat) (@instOfNatNat (0 : Nat))) _v2 _v3)) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat)))
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1))
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.startConfig _v0 _v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat))) _v2 _v3))) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine))) (@And (@Eq.{(0 + 1)} (@Nat)
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1))
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.deadline _v0 _v1)) (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0}
  (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 _v1)))) (@And.right (∀ (_v6 : (@Nat)),
(∀ (_v7 : (@LT.lt.{0} (@Nat) (@instLTNat) _v6
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1)))),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) _v6 (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.startConfig _v0 _v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) _v2 _v3))) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v6
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.startConfig _v0 _v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat))) _v2 _v3))) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine)))))) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat)))
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1))
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.startConfig _v0 _v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat))) _v2 _v3)) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.finalConfig _v0 _v1 (@OfNat.ofNat.{0} (@Nat) (0 :
  Nat) (@instOfNatNat (0 : Nat))) _v2 _v3)) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat)))
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1))
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.startConfig _v0 _v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat))) _v2 _v3))) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine))) (@And (@Eq.{(0 + 1)} (@Nat)
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1))
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.deadline _v0 _v1)) (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0}
  (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 _v1)))))
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.gate_first_arrival
  _v0 _v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v2 _v3 _v4)))));
(@id.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1)))) (@Decidable.byContradiction (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8
  : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v0) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))) _v0) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v1))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v0)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))) _v0) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v1))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (fun (_v7 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (8 : Nat)
  (@instOfNatNat (8 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v0) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))) _v0) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v1))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))))) =>
(@PartACanonical.PrivateABI.a0040 _v0 _v1 _v5 _v6 _v7)))))))
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencedContentTape _v0 _v1
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1)) _v2 _v3)))))))) := by
  exact @SmallIngress.raw_gamma_start

-- Complete literal proposition for SmallIngress.raw_gamma_start; original proof reused.
theorem PartACanonical.Surface.m0438 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ (_v2 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v0)),
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v4 : (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.tagMatches (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1) (@Fin.append.{(0 + 1)} _v0 _v1 (@Bool) _v2 _v3))
  (@Bool.true))),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SmallIngress.producer)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SmallIngress.producer)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.installClock
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1))
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.contentClock _v0 _v1)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1))) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat
  (7 : Nat)))) (@Pnp3.Complexity.Uniform.V1.initialConfig (@SmallIngress.producer)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v0 _v1 _v2 _v3))) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SmallIngress.producer))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1)) (@SmallIngress.q (@OfNat.ofNat.{0} (@Nat) (124 : Nat) (@instOfNatNat (124 : Nat)))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (let _v5 : (@LE.le.{0} (@Nat) (@instLENat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  _v0 _v1))) := (@And.left (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1))) (@LE.le.{0} (@Nat) (@instLENat) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.installClock
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1))
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1))) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.resource_bounds
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)));
(let _v6 : (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1)) := (@And.right (@Eq.{(0 + 1)} (@Nat)
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1))
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.deadline _v0 _v1)) (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0}
  (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 _v1)) (@And.right (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat)))
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1))
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.startConfig _v0 _v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat))) _v2 _v3))) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine))) (@And (@Eq.{(0 + 1)} (@Nat)
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1))
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.deadline _v0 _v1)) (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0}
  (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 _v1))) (@And.right (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat)))
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1))
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.startConfig _v0 _v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat))) _v2 _v3)) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.finalConfig _v0 _v1 (@OfNat.ofNat.{0} (@Nat) (0 :
  Nat) (@instOfNatNat (0 : Nat))) _v2 _v3)) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat)))
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1))
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.startConfig _v0 _v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat))) _v2 _v3))) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine))) (@And (@Eq.{(0 + 1)} (@Nat)
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1))
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.deadline _v0 _v1)) (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0}
  (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 _v1)))) (@And.right (∀ (_v6 : (@Nat)),
(∀ (_v7 : (@LT.lt.{0} (@Nat) (@instLTNat) _v6
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1)))),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) _v6 (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.startConfig _v0 _v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) _v2 _v3))) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v6
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.startConfig _v0 _v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat))) _v2 _v3))) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine)))))) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat)))
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1))
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.startConfig _v0 _v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat))) _v2 _v3)) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.finalConfig _v0 _v1 (@OfNat.ofNat.{0} (@Nat) (0 :
  Nat) (@instOfNatNat (0 : Nat))) _v2 _v3)) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat)))
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1))
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.startConfig _v0 _v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat))) _v2 _v3))) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.machine))) (@And (@Eq.{(0 + 1)} (@Nat)
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1))
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.deadline _v0 _v1)) (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0}
  (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 _v1)))))
  (@Pnp3.Complexity.Uniform.V1.FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.gate_first_arrival
  _v0 _v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v2 _v3 _v4)))));
(@id.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1)))) (@Decidable.byContradiction (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8
  : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v0) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))) _v0) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v1))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v0)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))) _v0) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v1))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (fun (_v7 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (8 : Nat)
  (@instOfNatNat (8 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v0) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v1)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))) _v0) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v1))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))))) =>
(@PartACanonical.PrivateABI.a0040 _v0 _v1 _v5 _v6 _v7)))))))
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencedContentTape _v0 _v1
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0
  _v1)) _v2 _v3)))))))) := by
  exact @SmallIngress.raw_gamma_start

-- Independent literal expected type for StandardTMBridgeClosure.compile.eq_1.
noncomputable def PartACanonical.Types.p0758 :
(∀ (_v0 : (@Pnp3.Complexity.Uniform.V1.UniformTM)),
(∀ (_v1 : (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool)))),
(@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@Turing.TM0.Stmt.{0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool)))))) (@StandardTMBridgeClosure.compile _v0
  (@Option.none.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0}
  (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) _v1) (@Option.some.{0} (@Prod.{0, 0} (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@Turing.TM0.Stmt.{0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))))) (@Prod.mk.{0, 0} (@Option.{0} (@Prod.{0,
  0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat
  (4 : Nat)))))) (@Turing.TM0.Stmt.{0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool)))) (@Option.some.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.start _v0) (@OfNat.ofNat.{0} (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat))) (@PartACanonical.PrivateABI.a0050) (0 : Nat))))) (@Turing.TM0.Stmt.write.{0} (@Prod.{0,
  0} (@Bool) (@Option.{0} (@Bool))) (@Prod.mk.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@Bool.true) (@Prod.snd.{0, 0} (@Bool)
  (@Option.{0} (@Bool)) _v1)))))))) := by
  exact @StandardTMBridgeClosure.compile.eq_1

-- Complete literal proposition for StandardTMBridgeClosure.compile.eq_1; original proof reused.
theorem PartACanonical.Surface.m0451 :
(∀ (_v0 : (@Pnp3.Complexity.Uniform.V1.UniformTM)),
(∀ (_v1 : (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool)))),
(@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@Turing.TM0.Stmt.{0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool)))))) (@StandardTMBridgeClosure.compile _v0
  (@Option.none.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0}
  (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) _v1) (@Option.some.{0} (@Prod.{0, 0} (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@Turing.TM0.Stmt.{0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))))) (@Prod.mk.{0, 0} (@Option.{0} (@Prod.{0,
  0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat
  (4 : Nat)))))) (@Turing.TM0.Stmt.{0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool)))) (@Option.some.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.start _v0) (@OfNat.ofNat.{0} (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat))) (@PartACanonical.PrivateABI.a0050) (0 : Nat))))) (@Turing.TM0.Stmt.write.{0} (@Prod.{0,
  0} (@Bool) (@Option.{0} (@Bool))) (@Prod.mk.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@Bool.true) (@Prod.snd.{0, 0} (@Bool)
  (@Option.{0} (@Bool)) _v1)))))))) := by
  exact @StandardTMBridgeClosure.compile.eq_1

-- Independent literal expected type for StandardTMBridgeClosure.compile.eq_2.
noncomputable def PartACanonical.Types.p0759 :
(∀ (_v0 : (@Pnp3.Complexity.Uniform.V1.UniformTM)),
(∀ (_v1 : (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool)))),
(∀ (_v2 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0))),
(∀ (_v3 : (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@Turing.TM0.Stmt.{0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool)))))) (@StandardTMBridgeClosure.compile _v0
  (@Option.some.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0}
  (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v2 _v3)) _v1) (@ite.{(0 + 1)} (@Option.{0}
  (@Prod.{0, 0} (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@Turing.TM0.Stmt.{0} (@Prod.{0, 0} (@Bool)
  (@Option.{0} (@Bool)))))) (@Eq.{(0 + 1)} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v3
  (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@PartACanonical.PrivateABI.a0050) (0 : Nat))))
  (@instDecidableEqFin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v3 (@OfNat.ofNat.{0} (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat))) (@PartACanonical.PrivateABI.a0050) (0 : Nat)))) (@ite.{(0 + 1)} (@Option.{0} (@Prod.{0,
  0} (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0}
  (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@Turing.TM0.Stmt.{0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))))))
  (@Or (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v0)) (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v0)))
  (@instDecidableOr (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v0)) (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v0))
  (@instDecidableEqFin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v0)) (@instDecidableEqFin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v0)))
  (@Option.none.{0} (@Prod.{0, 0} (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0))
  (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@Turing.TM0.Stmt.{0} (@Prod.{0, 0} (@Bool)
  (@Option.{0} (@Bool)))))) (let _v4 : (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) := (@Pnp3.Complexity.Uniform.V1.UniformTM.step
  _v0 _v2 (@Prod.snd.{0, 0} (@Bool) (@Option.{0} (@Bool)) _v1));
(@Option.some.{0} (@Prod.{0, 0} (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0))
  (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@Turing.TM0.Stmt.{0} (@Prod.{0, 0} (@Bool)
  (@Option.{0} (@Bool))))) (@Prod.mk.{0, 0} (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@Turing.TM0.Stmt.{0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool)))) (@Option.some.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Prod.fst.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) _v4) (@PartACanonical.PrivateABI.a0049
  (@Prod.snd.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Prod.snd.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) _v4))))) (@Turing.TM0.Stmt.write.{0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool)))
  (@Prod.mk.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@Prod.fst.{0, 0} (@Bool) (@Option.{0} (@Bool)) _v1) (@Prod.fst.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Prod.snd.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) _v4)))))))) (@ite.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Option.{0} (@Prod.{0, 0}
  (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4
  : Nat)))))) (@Turing.TM0.Stmt.{0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool)))))) (@Eq.{(0 + 1)} (@Fin (@OfNat.ofNat.{0}
  (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v3 (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))) (1 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))
  (@PartACanonical.PrivateABI.a0050) (1 : Nat)))) (@instDecidableEqFin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat
  (4 : Nat))) _v3 (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (1 : Nat)
  (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@PartACanonical.PrivateABI.a0050) (1 :
  Nat)))) (@Option.some.{0} (@Prod.{0, 0} (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@Turing.TM0.Stmt.{0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))))) (@Prod.mk.{0, 0} (@Option.{0} (@Prod.{0,
  0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat
  (4 : Nat)))))) (@Turing.TM0.Stmt.{0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool)))) (@Option.some.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))) _v2 (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))
  (@PartACanonical.PrivateABI.a0050) (0 : Nat))))) (@ite.{(0 + 1)} (@Turing.TM0.Stmt.{0} (@Prod.{0, 0} (@Bool)
  (@Option.{0} (@Bool)))) (@Eq.{(0 + 1)} (@Bool) (@Prod.fst.{0, 0} (@Bool) (@Option.{0} (@Bool)) _v1) (@Bool.true))
  (@instDecidableEqBool (@Prod.fst.{0, 0} (@Bool) (@Option.{0} (@Bool)) _v1) (@Bool.true)) (@Turing.TM0.Stmt.write.{0}
  (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v1) (@Turing.TM0.Stmt.move.{0} (@Prod.{0, 0} (@Bool) (@Option.{0}
  (@Bool))) (@Turing.Dir.left))))) (@ite.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@Turing.TM0.Stmt.{0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool)))))) (@Eq.{(0 + 1)} (@Fin (@OfNat.ofNat.{0}
  (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v3 (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))) (2 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))
  (@PartACanonical.PrivateABI.a0050) (2 : Nat)))) (@instDecidableEqFin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat
  (4 : Nat))) _v3 (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (2 : Nat)
  (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@PartACanonical.PrivateABI.a0050) (2 :
  Nat)))) (@Option.some.{0} (@Prod.{0, 0} (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@Turing.TM0.Stmt.{0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))))) (@Prod.mk.{0, 0} (@Option.{0} (@Prod.{0,
  0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat
  (4 : Nat)))))) (@Turing.TM0.Stmt.{0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool)))) (@Option.some.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))) _v2 (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))
  (@PartACanonical.PrivateABI.a0050) (0 : Nat))))) (@Turing.TM0.Stmt.write.{0} (@Prod.{0, 0} (@Bool) (@Option.{0}
  (@Bool))) _v1))) (@Option.some.{0} (@Prod.{0, 0} (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@Turing.TM0.Stmt.{0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))))) (@Prod.mk.{0, 0} (@Option.{0} (@Prod.{0,
  0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat
  (4 : Nat)))))) (@Turing.TM0.Stmt.{0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool)))) (@Option.some.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))) _v2 (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))
  (@PartACanonical.PrivateABI.a0050) (0 : Nat))))) (@Turing.TM0.Stmt.move.{0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool)))
  (@Turing.Dir.right)))))))))))) := by
  exact @StandardTMBridgeClosure.compile.eq_2

-- Complete literal proposition for StandardTMBridgeClosure.compile.eq_2; original proof reused.
theorem PartACanonical.Surface.m0452 :
(∀ (_v0 : (@Pnp3.Complexity.Uniform.V1.UniformTM)),
(∀ (_v1 : (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool)))),
(∀ (_v2 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0))),
(∀ (_v3 : (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@Turing.TM0.Stmt.{0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool)))))) (@StandardTMBridgeClosure.compile _v0
  (@Option.some.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0}
  (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v2 _v3)) _v1) (@ite.{(0 + 1)} (@Option.{0}
  (@Prod.{0, 0} (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@Turing.TM0.Stmt.{0} (@Prod.{0, 0} (@Bool)
  (@Option.{0} (@Bool)))))) (@Eq.{(0 + 1)} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v3
  (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@PartACanonical.PrivateABI.a0050) (0 : Nat))))
  (@instDecidableEqFin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v3 (@OfNat.ofNat.{0} (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat))) (@PartACanonical.PrivateABI.a0050) (0 : Nat)))) (@ite.{(0 + 1)} (@Option.{0} (@Prod.{0,
  0} (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0}
  (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@Turing.TM0.Stmt.{0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))))))
  (@Or (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v0)) (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v0)))
  (@instDecidableOr (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v0)) (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v0))
  (@instDecidableEqFin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept _v0)) (@instDecidableEqFin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.reject _v0)))
  (@Option.none.{0} (@Prod.{0, 0} (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0))
  (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@Turing.TM0.Stmt.{0} (@Prod.{0, 0} (@Bool)
  (@Option.{0} (@Bool)))))) (let _v4 : (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) := (@Pnp3.Complexity.Uniform.V1.UniformTM.step
  _v0 _v2 (@Prod.snd.{0, 0} (@Bool) (@Option.{0} (@Bool)) _v1));
(@Option.some.{0} (@Prod.{0, 0} (@Option.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0))
  (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@Turing.TM0.Stmt.{0} (@Prod.{0, 0} (@Bool)
  (@Option.{0} (@Bool))))) (@Prod.mk.{0, 0} (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@Turing.TM0.Stmt.{0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool)))) (@Option.some.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Prod.fst.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) _v4) (@PartACanonical.PrivateABI.a0049
  (@Prod.snd.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Prod.snd.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) _v4))))) (@Turing.TM0.Stmt.write.{0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool)))
  (@Prod.mk.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@Prod.fst.{0, 0} (@Bool) (@Option.{0} (@Bool)) _v1) (@Prod.fst.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Prod.snd.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) _v4)))))))) (@ite.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Option.{0} (@Prod.{0, 0}
  (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4
  : Nat)))))) (@Turing.TM0.Stmt.{0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool)))))) (@Eq.{(0 + 1)} (@Fin (@OfNat.ofNat.{0}
  (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v3 (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))) (1 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))
  (@PartACanonical.PrivateABI.a0050) (1 : Nat)))) (@instDecidableEqFin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat
  (4 : Nat))) _v3 (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (1 : Nat)
  (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@PartACanonical.PrivateABI.a0050) (1 :
  Nat)))) (@Option.some.{0} (@Prod.{0, 0} (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@Turing.TM0.Stmt.{0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))))) (@Prod.mk.{0, 0} (@Option.{0} (@Prod.{0,
  0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat
  (4 : Nat)))))) (@Turing.TM0.Stmt.{0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool)))) (@Option.some.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))) _v2 (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))
  (@PartACanonical.PrivateABI.a0050) (0 : Nat))))) (@ite.{(0 + 1)} (@Turing.TM0.Stmt.{0} (@Prod.{0, 0} (@Bool)
  (@Option.{0} (@Bool)))) (@Eq.{(0 + 1)} (@Bool) (@Prod.fst.{0, 0} (@Bool) (@Option.{0} (@Bool)) _v1) (@Bool.true))
  (@instDecidableEqBool (@Prod.fst.{0, 0} (@Bool) (@Option.{0} (@Bool)) _v1) (@Bool.true)) (@Turing.TM0.Stmt.write.{0}
  (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) _v1) (@Turing.TM0.Stmt.move.{0} (@Prod.{0, 0} (@Bool) (@Option.{0}
  (@Bool))) (@Turing.Dir.left))))) (@ite.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@Turing.TM0.Stmt.{0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool)))))) (@Eq.{(0 + 1)} (@Fin (@OfNat.ofNat.{0}
  (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v3 (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))) (2 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))
  (@PartACanonical.PrivateABI.a0050) (2 : Nat)))) (@instDecidableEqFin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat
  (4 : Nat))) _v3 (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (2 : Nat)
  (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@PartACanonical.PrivateABI.a0050) (2 :
  Nat)))) (@Option.some.{0} (@Prod.{0, 0} (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@Turing.TM0.Stmt.{0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))))) (@Prod.mk.{0, 0} (@Option.{0} (@Prod.{0,
  0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat
  (4 : Nat)))))) (@Turing.TM0.Stmt.{0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool)))) (@Option.some.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))) _v2 (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))
  (@PartACanonical.PrivateABI.a0050) (0 : Nat))))) (@Turing.TM0.Stmt.write.{0} (@Prod.{0, 0} (@Bool) (@Option.{0}
  (@Bool))) _v1))) (@Option.some.{0} (@Prod.{0, 0} (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@Turing.TM0.Stmt.{0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))))) (@Prod.mk.{0, 0} (@Option.{0} (@Prod.{0,
  0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat
  (4 : Nat)))))) (@Turing.TM0.Stmt.{0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool)))) (@Option.some.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))) _v2 (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))
  (@PartACanonical.PrivateABI.a0050) (0 : Nat))))) (@Turing.TM0.Stmt.move.{0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool)))
  (@Turing.Dir.right)))))))))))) := by
  exact @StandardTMBridgeClosure.compile.eq_2
