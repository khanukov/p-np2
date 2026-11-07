import Tests.PartACanonicalABI
import Tests.PartAG2InterfaceTests

/-! Infrastructure: mechanical literal restatements of this exact original API.
Proof terms are reused; these are not independently authored correctness proofs.
Type pins, theorem mirrors and direct roots remain separate manifests. -/
set_option autoImplicit false

-- Independent literal expected type for SerializedBodyRefinement.getAbort.
noncomputable def PartACanonical.Types.p0692 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(@Fin (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))))) := by
  exact @SerializedBodyRefinement.getAbort

-- Independent literal expected type for SerializedBodyRefinement.getBody.
noncomputable def PartACanonical.Types.p0693 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))))),
(∀ (_v1 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(@Fin (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat)))))) := by
  exact @SerializedBodyRefinement.getBody

-- Independent literal expected type for SerializedBodyRefinement.getEntry.
noncomputable def PartACanonical.Types.p0694 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))))),
(∀ (_v1 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(@Fin (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat)))))) := by
  exact @SerializedBodyRefinement.getEntry

-- Independent literal expected type for SerializedBodyRefinement.getExit.
noncomputable def PartACanonical.Types.p0695 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))))),
(∀ (_v1 : (@Bool)),
(∀ (_v2 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(@Fin (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))))))) := by
  exact @SerializedBodyRefinement.getExit

-- Independent literal expected type for SerializedBodyRefinement.reader.
noncomputable def PartACanonical.Types.p0696 :
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
(∀ (_v14 : (@Nat)),
(∀ (_v15 : (∀ (_v15 : (@Fin _v3)),
(@Bool))),
(∀ (_v16 : (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v9 _v10) _v8)),
(∀ (_v17 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v4)),
(∀ (_v18 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 _v5)),
(∀ (_v19 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v6)),
(∀ (_v20 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v5 _v6) _v7)),
(∀ (_v21 : (@Eq.{(0 + 1)} (@Nat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v7 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))))),
(∀ (_v22 : (∀ (_v22 : (@Nat)),
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) _v22 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 _v22) (@_v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v22 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))))),
(∀ (_v23 : (∀ (_v23 : (@Nat)),
(∀ (_v24 : (@Nat)),
(∀ (_v25 : (@LE.le.{0} (@Nat) (@instLENat) _v23 _v24)),
(∀ (_v26 : (@LE.le.{0} (@Nat) (@instLENat) _v24 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@LE.le.{0} (@Nat) (@instLENat) (@_v1 _v23) (@_v1 _v24))))))),
(∀ (_v24 : (∀ (_v24 : (@Nat)),
(∀ (_v25 : (@LE.le.{0} (@Nat) (@instLENat) _v24 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 (@_v1 _v24)) (@Option.none.{0} (@Bool)))))),
(∀ (_v25 : (∀ (_v25 : (@Nat)),
(∀ (_v26 : (@Nat)),
(∀ (_v27 : (@LT.lt.{0} (@Nat) (@instLTNat) _v25 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(∀ (_v28 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 _v25) _v26)),
(∀ (_v29 : (@LT.lt.{0} (@Nat) (@instLTNat) _v26 (@_v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v25 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))),
(@Exists.{(0 + 1)} (@Bool) (fun (_v30 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v26) (@Option.some.{0} (@Bool) _v30)))))))))),
(∀ (_v26 : (@Eq.{(0 + 1)} (@Nat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@_v1 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v8) (@OfNat.ofNat.{0} (@Nat)
  (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v27 : (@Eq.{(0 + 1)} (@Nat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v1 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) _v8)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v28 : (∀ (_v28 : (@Nat)),
(∀ (_v29 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v28)),
(∀ (_v30 : (@LT.lt.{0} (@Nat) (@instLTNat) _v28 (@_v1 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v28) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat)
  (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v28 (@_v1
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) _v9) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v28 (@_v1 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))
  _v9)))))))),
(∀ (_v29 : (∀ (_v29 : (@Nat)),
(∀ (_v30 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))
  _v29)),
(∀ (_v31 : (@LT.lt.{0} (@Nat) (@instLTNat) _v29 (@_v1 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 :
  Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v29) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat)
  (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v29 (@_v1
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))) _v10) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v29 (@_v1 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))))
  _v10)))))))),
(∀ (_v30 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v3) (@Option.none.{0} (@Bool)))),
(∀ (_v31 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v4) (@Option.none.{0} (@Bool)))),
(∀ (_v32 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v5) (@Option.none.{0} (@Bool)))),
(∀ (_v33 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v7) (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v34 : (∀ (_v34 : (@Nat)),
(∀ (_v35 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v34)),
(∀ (_v36 : (@LT.lt.{0} (@Nat) (@instLTNat) _v34 _v4)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v37 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v34) (@Option.some.{0} (@Bool) _v37)))))))),
(∀ (_v35 : (∀ (_v35 : (@Nat)),
(∀ (_v36 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 _v35)),
(∀ (_v37 : (@LT.lt.{0} (@Nat) (@instLTNat) _v35 _v5)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v38 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v35) (@Option.some.{0} (@Bool) _v38)))))))),
(∀ (_v36 : (∀ (_v36 : (@Nat)),
(∀ (_v37 : (@LT.lt.{0} (@Nat) (@instLTNat) _v5 _v36)),
(∀ (_v38 : (@LE.le.{0} (@Nat) (@instLENat) _v36 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v5 _v6))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v36) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v37 : (∀ (_v37 : (@Nat)),
(∀ (_v38 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v5 _v6) _v37)),
(∀ (_v39 : (@LT.lt.{0} (@Nat) (@instLTNat) _v37 _v7)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v37) (@Option.none.{0} (@Bool))))))),
(∀ (_v38 : (∀ (_v38 : (@LT.lt.{0} (@Nat) (@instLTNat) _v11 _v3)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v11) (@Option.none.{0} (@Bool))))),
(∀ (_v39 : (∀ (_v39 : (@Nat)),
(∀ (_v40 : (@LT.lt.{0} (@Nat) (@instLTNat) _v11 _v39)),
(∀ (_v41 : (@LT.lt.{0} (@Nat) (@instLTNat) _v39 _v3)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v39) (@Option.some.{0} (@Bool) (@_v15 (@Fin.mk _v3 _v39 _v41)))))))),
(∀ (_v40 : (@LE.le.{0} (@Nat) (@instLENat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))
  _v14)),
(∀ (_v41 : (@LT.lt.{0} (@Nat) (@instLTNat) _v14 (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13))),
(∀ (_v42 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13))),
(let _v43 : (∀ (_v43 : (@Nat)),
(@Option.{0} (@Bool))) := (fun (_v43 : (@Nat)) =>
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) _v43 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@_v1 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) _v10) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@instDecidableEqNat _v43 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v1 (@OfNat.ofNat.{0}
  (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) _v10) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))
  (@Option.some.{0} (@Bool) (@Bool.true)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) _v43 (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v1 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat
  (4 : Nat)))) _v9)) (@instDecidableEqNat _v43 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@_v1 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v9)) (@Option.some.{0} (@Bool)
  (@Bool.false)) (@_v2 _v43))));
(let _v44 : (@Pnp3.Complexity.Uniform.V1.Config (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v12
  _v13) := (@Pnp3.Complexity.Uniform.V1.Config.mk (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v12
  _v13 (@SerializedBodyRefinement.getEntry _v0 (@SerializedBody.sourceMode _v3 _v15 _v11)) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13) (@_v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  _v42) (fun (_v44 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13))) =>
(@_v2 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13) _v44))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v45 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v45 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@And
  (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v12 _v13) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v12 _v13
  _v45 _v44) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v12 _v13 (@ite.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine))) (@Eq.{(0 + 1)} (@Nat) _v9 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@instDecidableEqNat _v9 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@SerializedBodyRefinement.getAbort (@SerializedBody.sourceMode _v3 _v15 _v11)) (@SerializedBodyRefinement.getExit _v0
  (@Pnp4.Frontier.ContractExpansion.padRead _v3 _v15 _v11) (@SerializedBody.sourceMode _v3 _v15 (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat))))))) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13) (@_v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))) _v42) (fun (_v46 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13))) =>
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) _v9 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat)))) (@instDecidableEqNat _v9 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@_v2 (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13) _v46)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@LT.lt.{0} (@Nat)
  (@instLTNat) _v11 _v3) (@Nat.decLt _v11 _v3) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13) _v46) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v11 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@instDecidableEqNat
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13) _v46) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))
  (@Option.none.{0} (@Bool)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13) _v46) _v11) (@instDecidableEqNat (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13) _v46) _v11) (@Option.some.{0} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.padRead _v3 _v15 _v11)) (@_v43 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v12
  _v13) _v46)))) (@_v43 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13) _v46))))))) (∀ (_v46 : (@Nat)),
(∀ (_v47 : (@LE.le.{0} (@Nat) (@instLENat) _v46 _v45)),
(@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v12 _v13
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v12 _v13 _v46
  _v44))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @SerializedBodyRefinement.reader

-- Complete literal proposition for SerializedBodyRefinement.reader; original proof reused.
theorem PartACanonical.Surface.m0422 :
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
(∀ (_v14 : (@Nat)),
(∀ (_v15 : (∀ (_v15 : (@Fin _v3)),
(@Bool))),
(∀ (_v16 : (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v9 _v10) _v8)),
(∀ (_v17 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v4)),
(∀ (_v18 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 _v5)),
(∀ (_v19 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v6)),
(∀ (_v20 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v5 _v6) _v7)),
(∀ (_v21 : (@Eq.{(0 + 1)} (@Nat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v7 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))))),
(∀ (_v22 : (∀ (_v22 : (@Nat)),
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) _v22 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 _v22) (@_v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v22 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))))),
(∀ (_v23 : (∀ (_v23 : (@Nat)),
(∀ (_v24 : (@Nat)),
(∀ (_v25 : (@LE.le.{0} (@Nat) (@instLENat) _v23 _v24)),
(∀ (_v26 : (@LE.le.{0} (@Nat) (@instLENat) _v24 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@LE.le.{0} (@Nat) (@instLENat) (@_v1 _v23) (@_v1 _v24))))))),
(∀ (_v24 : (∀ (_v24 : (@Nat)),
(∀ (_v25 : (@LE.le.{0} (@Nat) (@instLENat) _v24 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 (@_v1 _v24)) (@Option.none.{0} (@Bool)))))),
(∀ (_v25 : (∀ (_v25 : (@Nat)),
(∀ (_v26 : (@Nat)),
(∀ (_v27 : (@LT.lt.{0} (@Nat) (@instLTNat) _v25 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(∀ (_v28 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 _v25) _v26)),
(∀ (_v29 : (@LT.lt.{0} (@Nat) (@instLTNat) _v26 (@_v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v25 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))),
(@Exists.{(0 + 1)} (@Bool) (fun (_v30 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v26) (@Option.some.{0} (@Bool) _v30)))))))))),
(∀ (_v26 : (@Eq.{(0 + 1)} (@Nat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@_v1 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v8) (@OfNat.ofNat.{0} (@Nat)
  (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v27 : (@Eq.{(0 + 1)} (@Nat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v1 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) _v8)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v28 : (∀ (_v28 : (@Nat)),
(∀ (_v29 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v28)),
(∀ (_v30 : (@LT.lt.{0} (@Nat) (@instLTNat) _v28 (@_v1 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v28) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat)
  (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v28 (@_v1
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) _v9) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v28 (@_v1 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))
  _v9)))))))),
(∀ (_v29 : (∀ (_v29 : (@Nat)),
(∀ (_v30 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))
  _v29)),
(∀ (_v31 : (@LT.lt.{0} (@Nat) (@instLTNat) _v29 (@_v1 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 :
  Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v29) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat)
  (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v29 (@_v1
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))) _v10) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v29 (@_v1 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))))
  _v10)))))))),
(∀ (_v30 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v3) (@Option.none.{0} (@Bool)))),
(∀ (_v31 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v4) (@Option.none.{0} (@Bool)))),
(∀ (_v32 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v5) (@Option.none.{0} (@Bool)))),
(∀ (_v33 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v7) (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v34 : (∀ (_v34 : (@Nat)),
(∀ (_v35 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v34)),
(∀ (_v36 : (@LT.lt.{0} (@Nat) (@instLTNat) _v34 _v4)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v37 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v34) (@Option.some.{0} (@Bool) _v37)))))))),
(∀ (_v35 : (∀ (_v35 : (@Nat)),
(∀ (_v36 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 _v35)),
(∀ (_v37 : (@LT.lt.{0} (@Nat) (@instLTNat) _v35 _v5)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v38 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v35) (@Option.some.{0} (@Bool) _v38)))))))),
(∀ (_v36 : (∀ (_v36 : (@Nat)),
(∀ (_v37 : (@LT.lt.{0} (@Nat) (@instLTNat) _v5 _v36)),
(∀ (_v38 : (@LE.le.{0} (@Nat) (@instLENat) _v36 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v5 _v6))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v36) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v37 : (∀ (_v37 : (@Nat)),
(∀ (_v38 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v5 _v6) _v37)),
(∀ (_v39 : (@LT.lt.{0} (@Nat) (@instLTNat) _v37 _v7)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v37) (@Option.none.{0} (@Bool))))))),
(∀ (_v38 : (∀ (_v38 : (@LT.lt.{0} (@Nat) (@instLTNat) _v11 _v3)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v11) (@Option.none.{0} (@Bool))))),
(∀ (_v39 : (∀ (_v39 : (@Nat)),
(∀ (_v40 : (@LT.lt.{0} (@Nat) (@instLTNat) _v11 _v39)),
(∀ (_v41 : (@LT.lt.{0} (@Nat) (@instLTNat) _v39 _v3)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v39) (@Option.some.{0} (@Bool) (@_v15 (@Fin.mk _v3 _v39 _v41)))))))),
(∀ (_v40 : (@LE.le.{0} (@Nat) (@instLENat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))
  _v14)),
(∀ (_v41 : (@LT.lt.{0} (@Nat) (@instLTNat) _v14 (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13))),
(∀ (_v42 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13))),
(let _v43 : (∀ (_v43 : (@Nat)),
(@Option.{0} (@Bool))) := (fun (_v43 : (@Nat)) =>
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) _v43 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@_v1 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) _v10) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@instDecidableEqNat _v43 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v1 (@OfNat.ofNat.{0}
  (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) _v10) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))
  (@Option.some.{0} (@Bool) (@Bool.true)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) _v43 (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v1 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat
  (4 : Nat)))) _v9)) (@instDecidableEqNat _v43 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@_v1 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v9)) (@Option.some.{0} (@Bool)
  (@Bool.false)) (@_v2 _v43))));
(let _v44 : (@Pnp3.Complexity.Uniform.V1.Config (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v12
  _v13) := (@Pnp3.Complexity.Uniform.V1.Config.mk (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v12
  _v13 (@SerializedBodyRefinement.getEntry _v0 (@SerializedBody.sourceMode _v3 _v15 _v11)) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13) (@_v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  _v42) (fun (_v44 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13))) =>
(@_v2 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13) _v44))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v45 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v45 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@And
  (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v12 _v13) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v12 _v13
  _v45 _v44) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v12 _v13 (@ite.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine))) (@Eq.{(0 + 1)} (@Nat) _v9 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@instDecidableEqNat _v9 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@SerializedBodyRefinement.getAbort (@SerializedBody.sourceMode _v3 _v15 _v11)) (@SerializedBodyRefinement.getExit _v0
  (@Pnp4.Frontier.ContractExpansion.padRead _v3 _v15 _v11) (@SerializedBody.sourceMode _v3 _v15 (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat))))))) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13) (@_v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))) _v42) (fun (_v46 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13))) =>
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) _v9 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat)))) (@instDecidableEqNat _v9 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@_v2 (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13) _v46)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@LT.lt.{0} (@Nat)
  (@instLTNat) _v11 _v3) (@Nat.decLt _v11 _v3) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13) _v46) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v11 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@instDecidableEqNat
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13) _v46) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))
  (@Option.none.{0} (@Bool)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13) _v46) _v11) (@instDecidableEqNat (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13) _v46) _v11) (@Option.some.{0} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.padRead _v3 _v15 _v11)) (@_v43 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v12
  _v13) _v46)))) (@_v43 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13) _v46))))))) (∀ (_v46 : (@Nat)),
(∀ (_v47 : (@LE.le.{0} (@Nat) (@instLENat) _v46 _v45)),
(@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v12 _v13
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v12 _v13 _v46
  _v44))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @SerializedBodyRefinement.reader

-- Independent literal expected type for SerializedBodyRefinement.reader_mirror.
noncomputable def PartACanonical.Types.p0697 :
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
(∀ (_v14 : (@Nat)),
(∀ (_v15 : (∀ (_v15 : (@Fin _v3)),
(@Bool))),
(∀ (_v16 : (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v9 _v10) _v8)),
(∀ (_v17 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v4)),
(∀ (_v18 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 _v5)),
(∀ (_v19 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v6)),
(∀ (_v20 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v5 _v6) _v7)),
(∀ (_v21 : (@Eq.{(0 + 1)} (@Nat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v7 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))))),
(∀ (_v22 : (∀ (_v22 : (@Nat)),
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) _v22 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 _v22) (@_v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v22 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))))),
(∀ (_v23 : (∀ (_v23 : (@Nat)),
(∀ (_v24 : (@Nat)),
(∀ (_v25 : (@LE.le.{0} (@Nat) (@instLENat) _v23 _v24)),
(∀ (_v26 : (@LE.le.{0} (@Nat) (@instLENat) _v24 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@LE.le.{0} (@Nat) (@instLENat) (@_v1 _v23) (@_v1 _v24))))))),
(∀ (_v24 : (∀ (_v24 : (@Nat)),
(∀ (_v25 : (@LE.le.{0} (@Nat) (@instLENat) _v24 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 (@_v1 _v24)) (@Option.none.{0} (@Bool)))))),
(∀ (_v25 : (∀ (_v25 : (@Nat)),
(∀ (_v26 : (@Nat)),
(∀ (_v27 : (@LT.lt.{0} (@Nat) (@instLTNat) _v25 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(∀ (_v28 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 _v25) _v26)),
(∀ (_v29 : (@LT.lt.{0} (@Nat) (@instLTNat) _v26 (@_v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v25 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))),
(@Exists.{(0 + 1)} (@Bool) (fun (_v30 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v26) (@Option.some.{0} (@Bool) _v30)))))))))),
(∀ (_v26 : (@Eq.{(0 + 1)} (@Nat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@_v1 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v8) (@OfNat.ofNat.{0} (@Nat)
  (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v27 : (@Eq.{(0 + 1)} (@Nat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v1 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) _v8)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v28 : (∀ (_v28 : (@Nat)),
(∀ (_v29 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v28)),
(∀ (_v30 : (@LT.lt.{0} (@Nat) (@instLTNat) _v28 (@_v1 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v28) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat)
  (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v28 (@_v1
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) _v9) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v28 (@_v1 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))
  _v9)))))))),
(∀ (_v29 : (∀ (_v29 : (@Nat)),
(∀ (_v30 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))
  _v29)),
(∀ (_v31 : (@LT.lt.{0} (@Nat) (@instLTNat) _v29 (@_v1 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 :
  Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v29) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat)
  (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v29 (@_v1
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))) _v10) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v29 (@_v1 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))))
  _v10)))))))),
(∀ (_v30 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v3) (@Option.none.{0} (@Bool)))),
(∀ (_v31 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v4) (@Option.none.{0} (@Bool)))),
(∀ (_v32 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v5) (@Option.none.{0} (@Bool)))),
(∀ (_v33 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v7) (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v34 : (∀ (_v34 : (@Nat)),
(∀ (_v35 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v34)),
(∀ (_v36 : (@LT.lt.{0} (@Nat) (@instLTNat) _v34 _v4)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v37 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v34) (@Option.some.{0} (@Bool) _v37)))))))),
(∀ (_v35 : (∀ (_v35 : (@Nat)),
(∀ (_v36 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 _v35)),
(∀ (_v37 : (@LT.lt.{0} (@Nat) (@instLTNat) _v35 _v5)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v38 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v35) (@Option.some.{0} (@Bool) _v38)))))))),
(∀ (_v36 : (∀ (_v36 : (@Nat)),
(∀ (_v37 : (@LT.lt.{0} (@Nat) (@instLTNat) _v5 _v36)),
(∀ (_v38 : (@LE.le.{0} (@Nat) (@instLENat) _v36 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v5 _v6))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v36) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v37 : (∀ (_v37 : (@Nat)),
(∀ (_v38 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v5 _v6) _v37)),
(∀ (_v39 : (@LT.lt.{0} (@Nat) (@instLTNat) _v37 _v7)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v37) (@Option.none.{0} (@Bool))))))),
(∀ (_v38 : (∀ (_v38 : (@LT.lt.{0} (@Nat) (@instLTNat) _v11 _v3)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v11) (@Option.none.{0} (@Bool))))),
(∀ (_v39 : (∀ (_v39 : (@Nat)),
(∀ (_v40 : (@LT.lt.{0} (@Nat) (@instLTNat) _v11 _v39)),
(∀ (_v41 : (@LT.lt.{0} (@Nat) (@instLTNat) _v39 _v3)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v39) (@Option.some.{0} (@Bool) (@_v15 (@Fin.mk _v3 _v39 _v41)))))))),
(∀ (_v40 : (@LE.le.{0} (@Nat) (@instLENat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))
  _v14)),
(∀ (_v41 : (@LT.lt.{0} (@Nat) (@instLTNat) _v14 (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13))),
(∀ (_v42 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13))),
(let _v43 : (∀ (_v43 : (@Nat)),
(@Option.{0} (@Bool))) := (fun (_v43 : (@Nat)) =>
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) _v43 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@_v1 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) _v10) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@instDecidableEqNat _v43 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v1 (@OfNat.ofNat.{0}
  (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) _v10) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))
  (@Option.some.{0} (@Bool) (@Bool.true)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) _v43 (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v1 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat
  (4 : Nat)))) _v9)) (@instDecidableEqNat _v43 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@_v1 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v9)) (@Option.some.{0} (@Bool)
  (@Bool.false)) (@_v2 _v43))));
(let _v44 : (@Pnp3.Complexity.Uniform.V1.Config (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v12
  _v13) := (@Pnp3.Complexity.Uniform.V1.Config.mk (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v12
  _v13 (@SerializedBodyRefinement.getEntry _v0 (@SerializedBody.sourceMode _v3 _v15 _v11)) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13) (@_v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  _v42) (fun (_v44 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13))) =>
(@_v2 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13) _v44))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v45 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v45 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@And
  (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v12 _v13) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v12 _v13
  _v45 _v44) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v12 _v13 (@ite.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine))) (@Eq.{(0 + 1)} (@Nat) _v9 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@instDecidableEqNat _v9 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@SerializedBodyRefinement.getAbort (@SerializedBody.sourceMode _v3 _v15 _v11)) (@SerializedBodyRefinement.getExit _v0
  (@Pnp4.Frontier.ContractExpansion.padRead _v3 _v15 _v11) (@SerializedBody.sourceMode _v3 _v15 (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat))))))) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13) (@_v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))) _v42) (fun (_v46 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13))) =>
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) _v9 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat)))) (@instDecidableEqNat _v9 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@_v2 (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13) _v46)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@LT.lt.{0} (@Nat)
  (@instLTNat) _v11 _v3) (@Nat.decLt _v11 _v3) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13) _v46) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v11 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@instDecidableEqNat
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13) _v46) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))
  (@Option.none.{0} (@Bool)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13) _v46) _v11) (@instDecidableEqNat (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13) _v46) _v11) (@Option.some.{0} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.padRead _v3 _v15 _v11)) (@_v43 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v12
  _v13) _v46)))) (@_v43 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13) _v46))))))) (∀ (_v46 : (@Nat)),
(∀ (_v47 : (@LE.le.{0} (@Nat) (@instLENat) _v46 _v45)),
(@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v12 _v13
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v12 _v13 _v46
  _v44))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @SerializedBodyRefinement.reader_mirror

-- Complete literal proposition for SerializedBodyRefinement.reader_mirror; original proof reused.
theorem PartACanonical.Surface.m0423 :
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
(∀ (_v14 : (@Nat)),
(∀ (_v15 : (∀ (_v15 : (@Fin _v3)),
(@Bool))),
(∀ (_v16 : (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v9 _v10) _v8)),
(∀ (_v17 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v4)),
(∀ (_v18 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 _v5)),
(∀ (_v19 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v6)),
(∀ (_v20 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v5 _v6) _v7)),
(∀ (_v21 : (@Eq.{(0 + 1)} (@Nat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v7 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))))),
(∀ (_v22 : (∀ (_v22 : (@Nat)),
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) _v22 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 _v22) (@_v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v22 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))))),
(∀ (_v23 : (∀ (_v23 : (@Nat)),
(∀ (_v24 : (@Nat)),
(∀ (_v25 : (@LE.le.{0} (@Nat) (@instLENat) _v23 _v24)),
(∀ (_v26 : (@LE.le.{0} (@Nat) (@instLENat) _v24 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@LE.le.{0} (@Nat) (@instLENat) (@_v1 _v23) (@_v1 _v24))))))),
(∀ (_v24 : (∀ (_v24 : (@Nat)),
(∀ (_v25 : (@LE.le.{0} (@Nat) (@instLENat) _v24 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 (@_v1 _v24)) (@Option.none.{0} (@Bool)))))),
(∀ (_v25 : (∀ (_v25 : (@Nat)),
(∀ (_v26 : (@Nat)),
(∀ (_v27 : (@LT.lt.{0} (@Nat) (@instLTNat) _v25 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(∀ (_v28 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 _v25) _v26)),
(∀ (_v29 : (@LT.lt.{0} (@Nat) (@instLTNat) _v26 (@_v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v25 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))),
(@Exists.{(0 + 1)} (@Bool) (fun (_v30 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v26) (@Option.some.{0} (@Bool) _v30)))))))))),
(∀ (_v26 : (@Eq.{(0 + 1)} (@Nat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@_v1 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v8) (@OfNat.ofNat.{0} (@Nat)
  (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v27 : (@Eq.{(0 + 1)} (@Nat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v1 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) _v8)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v28 : (∀ (_v28 : (@Nat)),
(∀ (_v29 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v28)),
(∀ (_v30 : (@LT.lt.{0} (@Nat) (@instLTNat) _v28 (@_v1 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v28) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat)
  (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v28 (@_v1
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) _v9) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v28 (@_v1 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))
  _v9)))))))),
(∀ (_v29 : (∀ (_v29 : (@Nat)),
(∀ (_v30 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))
  _v29)),
(∀ (_v31 : (@LT.lt.{0} (@Nat) (@instLTNat) _v29 (@_v1 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 :
  Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v29) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat)
  (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v29 (@_v1
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))) _v10) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v29 (@_v1 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))))
  _v10)))))))),
(∀ (_v30 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v3) (@Option.none.{0} (@Bool)))),
(∀ (_v31 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v4) (@Option.none.{0} (@Bool)))),
(∀ (_v32 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v5) (@Option.none.{0} (@Bool)))),
(∀ (_v33 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v7) (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v34 : (∀ (_v34 : (@Nat)),
(∀ (_v35 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v34)),
(∀ (_v36 : (@LT.lt.{0} (@Nat) (@instLTNat) _v34 _v4)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v37 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v34) (@Option.some.{0} (@Bool) _v37)))))))),
(∀ (_v35 : (∀ (_v35 : (@Nat)),
(∀ (_v36 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 _v35)),
(∀ (_v37 : (@LT.lt.{0} (@Nat) (@instLTNat) _v35 _v5)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v38 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v35) (@Option.some.{0} (@Bool) _v38)))))))),
(∀ (_v36 : (∀ (_v36 : (@Nat)),
(∀ (_v37 : (@LT.lt.{0} (@Nat) (@instLTNat) _v5 _v36)),
(∀ (_v38 : (@LE.le.{0} (@Nat) (@instLENat) _v36 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v5 _v6))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v36) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v37 : (∀ (_v37 : (@Nat)),
(∀ (_v38 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v5 _v6) _v37)),
(∀ (_v39 : (@LT.lt.{0} (@Nat) (@instLTNat) _v37 _v7)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v37) (@Option.none.{0} (@Bool))))))),
(∀ (_v38 : (∀ (_v38 : (@LT.lt.{0} (@Nat) (@instLTNat) _v11 _v3)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v11) (@Option.none.{0} (@Bool))))),
(∀ (_v39 : (∀ (_v39 : (@Nat)),
(∀ (_v40 : (@LT.lt.{0} (@Nat) (@instLTNat) _v11 _v39)),
(∀ (_v41 : (@LT.lt.{0} (@Nat) (@instLTNat) _v39 _v3)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v39) (@Option.some.{0} (@Bool) (@_v15 (@Fin.mk _v3 _v39 _v41)))))))),
(∀ (_v40 : (@LE.le.{0} (@Nat) (@instLENat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))
  _v14)),
(∀ (_v41 : (@LT.lt.{0} (@Nat) (@instLTNat) _v14 (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13))),
(∀ (_v42 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13))),
(let _v43 : (∀ (_v43 : (@Nat)),
(@Option.{0} (@Bool))) := (fun (_v43 : (@Nat)) =>
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) _v43 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@_v1 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) _v10) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@instDecidableEqNat _v43 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v1 (@OfNat.ofNat.{0}
  (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) _v10) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))
  (@Option.some.{0} (@Bool) (@Bool.true)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) _v43 (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v1 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat
  (4 : Nat)))) _v9)) (@instDecidableEqNat _v43 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@_v1 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v9)) (@Option.some.{0} (@Bool)
  (@Bool.false)) (@_v2 _v43))));
(let _v44 : (@Pnp3.Complexity.Uniform.V1.Config (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v12
  _v13) := (@Pnp3.Complexity.Uniform.V1.Config.mk (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v12
  _v13 (@SerializedBodyRefinement.getEntry _v0 (@SerializedBody.sourceMode _v3 _v15 _v11)) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13) (@_v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  _v42) (fun (_v44 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13))) =>
(@_v2 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13) _v44))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v45 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v45 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@And
  (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v12 _v13) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v12 _v13
  _v45 _v44) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v12 _v13 (@ite.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine))) (@Eq.{(0 + 1)} (@Nat) _v9 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@instDecidableEqNat _v9 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@SerializedBodyRefinement.getAbort (@SerializedBody.sourceMode _v3 _v15 _v11)) (@SerializedBodyRefinement.getExit _v0
  (@Pnp4.Frontier.ContractExpansion.padRead _v3 _v15 _v11) (@SerializedBody.sourceMode _v3 _v15 (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat))))))) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13) (@_v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))) _v42) (fun (_v46 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13))) =>
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) _v9 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat)))) (@instDecidableEqNat _v9 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@_v2 (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13) _v46)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@LT.lt.{0} (@Nat)
  (@instLTNat) _v11 _v3) (@Nat.decLt _v11 _v3) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13) _v46) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v11 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@instDecidableEqNat
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13) _v46) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))
  (@Option.none.{0} (@Bool)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13) _v46) _v11) (@instDecidableEqNat (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13) _v46) _v11) (@Option.some.{0} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.padRead _v3 _v15 _v11)) (@_v43 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v12
  _v13) _v46)))) (@_v43 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13) _v46))))))) (∀ (_v46 : (@Nat)),
(∀ (_v47 : (@LE.le.{0} (@Nat) (@instLENat) _v46 _v45)),
(@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v12 _v13
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v12 _v13 _v46
  _v44))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @SerializedBodyRefinement.reader_mirror

-- Independent literal expected type for SerializedBodyRefinement.sourceMode_eq_1_mirror.
noncomputable def PartACanonical.Types.p0698 :
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
  Nat))) (@of_decide_eq_true (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@id.{0} (@Eq.{(0 + 1)}
  (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))) (@Bool.true)) (@Eq.refl.{(0 +
  1)} (@Bool) (@Bool.true))))) (@Fin.mk (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@of_decide_eq_true (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat)
  (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Nat.decLt
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 :
  Nat)))) (@id.{0} (@Eq.{(0 + 1)} (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 :
  Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Nat.decLt
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 :
  Nat))))) (@Bool.true)) (@Eq.refl.{(0 + 1)} (@Bool) (@Bool.true))))))) (fun (_v3 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat)
  _v2 _v0))) =>
(@Fin.mk (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat))) (@of_decide_eq_true (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@id.{0} (@Eq.{(0 + 1)}
  (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))) (@Bool.true)) (@Eq.refl.{(0 +
  1)} (@Bool) (@Bool.true))))))))))) := by
  exact @SerializedBodyRefinement.sourceMode_eq_1_mirror

-- Complete literal proposition for SerializedBodyRefinement.sourceMode_eq_1_mirror; original proof reused.
theorem PartACanonical.Surface.m0424 :
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
  Nat))) (@of_decide_eq_true (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@id.{0} (@Eq.{(0 + 1)}
  (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))) (@Bool.true)) (@Eq.refl.{(0 +
  1)} (@Bool) (@Bool.true))))) (@Fin.mk (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@of_decide_eq_true (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat)
  (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Nat.decLt
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 :
  Nat)))) (@id.{0} (@Eq.{(0 + 1)} (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 :
  Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Nat.decLt
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 :
  Nat))))) (@Bool.true)) (@Eq.refl.{(0 + 1)} (@Bool) (@Bool.true))))))) (fun (_v3 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat)
  _v2 _v0))) =>
(@Fin.mk (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat))) (@of_decide_eq_true (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@id.{0} (@Eq.{(0 + 1)}
  (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))) (@Bool.true)) (@Eq.refl.{(0 +
  1)} (@Bool) (@Bool.true))))))))))) := by
  exact @SerializedBodyRefinement.sourceMode_eq_1_mirror

-- Independent literal expected type for SerializedPositiveBody.initialized_node.
noncomputable def PartACanonical.Types.p0699 :
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
(∀ (_v18 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v5)),
(∀ (_v19 : (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v6)),
(let _v20 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation _v0);
(let _v21 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat))));
(let _v22 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v21 _v3) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat))));
(let _v23 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v0);
(∀ (_v24 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v8)),
(∀ (_v25 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v22 _v8) _v23)),
(∀ (_v26 : (∀ (_v26 : (@Nat)),
(∀ (_v27 : (@LE.le.{0} (@Nat) (@instLENat) _v7 _v26)),
(∀ (_v28 : (@LT.lt.{0} (@Nat) (@instLTNat) _v26 _v1)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v11 _v26) (@Option.some.{0} (@Bool) (@_v9 (@Fin.mk _v1 _v26 _v28)))))))),
(∀ (_v27 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v11 _v1) (@Option.none.{0} (@Bool)))),
(∀ (_v28 : (∀ (_v28 : (@Nat)),
(∀ (_v29 : (@LT.lt.{0} (@Nat) (@instLTNat) _v1 _v28)),
(∀ (_v30 : (@LT.lt.{0} (@Nat) (@instLTNat) _v28 _v21)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v11 _v28) (@Option.some.{0} (@Bool) (@Bool.false))))))),
(∀ (_v29 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v11 _v21) (@Option.none.{0} (@Bool)))),
(∀ (_v30 : (∀ (_v30 : (@Fin _v3)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v11 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v22 (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Fin.val _v3 _v30))) (@Option.some.{0} (@Bool) (@_v10 _v30))))),
(∀ (_v31 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v11 _v22) (@Option.none.{0} (@Bool)))),
(∀ (_v32 : (∀ (_v32 : (@Nat)),
(∀ (_v33 : (@LT.lt.{0} (@Nat) (@instLTNat) _v22 _v32)),
(∀ (_v34 : (@LE.le.{0} (@Nat) (@instLENat) _v32 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v22 _v8))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v11 _v32) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v33 : (∀ (_v33 : (@Nat)),
(∀ (_v34 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v22 _v8) _v33)),
(∀ (_v35 : (@LT.lt.{0} (@Nat) (@instLTNat) _v33 _v23)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v11 _v33) (@Option.none.{0} (@Bool))))))),
(∀ (_v34 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v11 _v23) (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v35 : (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter _v23 _v4 _v3 (@OfNat.ofNat.{0} (@Nat) (12 : Nat)
  (@instOfNatNat (12 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v20))),
(∀ (_v36 : (@LT.lt.{0} (@Nat) (@instLTNat) _v22 (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v20))),
(let _v37 : (∀ (_v37 : (@Nat)),
(@Nat)) := (@SerializedBody.delimiter _v23 _v4 _v3);
(let _v38 : (∀ (_v38 : (@Nat)),
(@Option.{0} (@Bool))) := (@SerializedBody.image _v11 _v23 _v4 _v3 _v5 _v6 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHSub.{0} (@Nat) (@instSubNat)) _v1 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) _v7 _v1)) (@OfNat.ofNat.{0} (@Nat)
  (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v6 _v5);
(let _v39 : (∀ (_v39 : (@Nat)),
(@Option.{0} (@Bool))) := (fun (_v39 : (@Nat)) =>
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) _v39 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v37 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@instDecidableEqNat _v39 (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v37 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Option.some.{0} (@Bool) (@Bool.true)) (@ite.{(0 + 1)}
  (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) _v39 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@_v37 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) _v5)) (@instDecidableEqNat _v39
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v37 (@OfNat.ofNat.{0} (@Nat) (6 :
  Nat) (@instOfNatNat (6 : Nat)))) _v5)) (@Option.some.{0} (@Bool) (@Bool.false)) (@_v38 _v39))));
(let _v40 : (∀ (_v40 : (@Nat)),
(@Option.{0} (@Bool))) := (fun (_v40 : (@Nat)) =>
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@Eq.{(0 + 1)} (@Nat) _v40 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v7 (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))) (@LT.lt.{0}
  (@Nat) (@instLTNat) _v40 _v1)) (@instDecidableAnd (@Eq.{(0 + 1)} (@Nat) _v40 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v7 (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))) (@LT.lt.{0}
  (@Nat) (@instLTNat) _v40 _v1) (@instDecidableEqNat _v40 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v7 (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))) (@Nat.decLt _v40 _v1))
  (@Option.none.{0} (@Bool)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@_v37
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v40) (@LT.lt.{0} (@Nat) (@instLTNat) _v40 (@_v37
  (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat)
  (@_v37 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v40) (@LT.lt.{0} (@Nat) (@instLTNat) _v40 (@_v37
  (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))) (@Nat.decLt (@_v37 (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))) _v40) (@Nat.decLt _v40 (@_v37 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 :
  Nat)))))) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v40 (@_v37 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (3
  : Nat) (@instOfNatNat (3 : Nat))))) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v40 (@_v37 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@HSub.hSub.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))))))
  (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@_v37 (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat)))) _v40) (@LT.lt.{0} (@Nat) (@instLTNat) _v40 (@_v37 (@OfNat.ofNat.{0} (@Nat) (12 : Nat)
  (@instOfNatNat (12 : Nat)))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@_v37 (@OfNat.ofNat.{0} (@Nat) (11 :
  Nat) (@instOfNatNat (11 : Nat)))) _v40) (@LT.lt.{0} (@Nat) (@instLTNat) _v40 (@_v37 (@OfNat.ofNat.{0} (@Nat) (12 : Nat)
  (@instOfNatNat (12 : Nat))))) (@Nat.decLt (@_v37 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) _v40)
  (@Nat.decLt _v40 (@_v37 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))))) (@Option.some.{0} (@Bool)
  (@Decidable.decide (@LE.le.{0} (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v40 (@_v37 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (3
  : Nat) (@instOfNatNat (3 : Nat)))) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v40 (@_v37 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (3
  : Nat) (@instOfNatNat (3 : Nat)))))) (@_v39 _v40)))));
(let _v41 : (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))) := (@ite.{(0 + 1)} (@Fin
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))) (@Eq.{(0 + 1)} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.padRead _v1 _v9 _v7) (@Bool.true)) (@instDecidableEqBool
  (@Pnp4.Frontier.ContractExpansion.padRead _v1 _v9 _v7) (@Bool.true)) (@ite.{(0 + 1)} (@Fin (@OfNat.ofNat.{0} (@Nat) (9 :
  Nat) (@instOfNatNat (9 : Nat)))) (@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead _v1 _v9
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v7 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@Bool.true)) (@instDecidableEqBool (@Pnp4.Frontier.ContractExpansion.padRead _v1 _v9
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v7 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@Bool.true)) (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9
  : Nat)))) (6 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@Nat.instNeZeroSucc
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))) (6 : Nat))) (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0}
  (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))) (5 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat
  (9 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))) (5 : Nat)))) (@ite.{(0 +
  1)} (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))) (@Eq.{(0 + 1)} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.padRead _v1 _v9 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v7 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Bool.true)) (@instDecidableEqBool
  (@Pnp4.Frontier.ContractExpansion.padRead _v1 _v9 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v7 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Bool.true)) (@OfNat.ofNat.{0} (@Fin
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))) (4 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (9 :
  Nat) (@instOfNatNat (9 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))) (4 :
  Nat))) (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))) (3 : Nat) (@Fin.instOfNat
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (8 : Nat)
  (@instOfNatNat (8 : Nat)))) (3 : Nat)))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v42 : (@Nat)) =>
(@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@_v37 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v20)) (fun (_v43 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v37 (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v20))) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v42 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (1073741824 : Nat) (@instOfNatNat (1073741824 : Nat))) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))) (@And (@Eq.{(0 + 1)}
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v0
  _v20) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v20 _v42
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v0 _v20
  (@SerializedBody.entry (@SerializedBody.sourceMode _v1 _v9 _v7)) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v0
  _v20) _v22 _v36) (fun (_v44 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v20))) =>
(@SerializedBody.prepared _v11 _v1 _v7 _v23 _v4 _v3 _v5 _v6 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v20)
  _v44))))) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v0 _v20 (@SerializedBodyRefinement.getExit _v41 (@Pnp4.Frontier.ContractExpansion.padRead
  _v1 _v9 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v7 (@OfNat.ofNat.{0} (@Nat) (2
  : Nat) (@instOfNatNat (2 : Nat))))) (@SerializedBody.sourceMode _v1 _v9 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v7 (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v20) (@_v37 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  _v43) (fun (_v44 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v20))) =>
(@_v40 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v20) _v44))))) (∀ (_v44 : (@Nat)),
(∀ (_v45 : (@LE.le.{0} (@Nat) (@instLENat) _v44 _v42)),
(@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v0 _v20
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v20 _v44
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v0 _v20
  (@SerializedBody.entry (@SerializedBody.sourceMode _v1 _v9 _v7)) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v0
  _v20) _v22 _v36) (fun (_v46 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v20))) =>
(@SerializedBody.prepared _v11 _v1 _v7 _v23 _v4 _v3 _v5 _v6 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v20)
  _v46)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @SerializedPositiveBody.initialized_node

-- Complete literal proposition for SerializedPositiveBody.initialized_node; original proof reused.
theorem PartACanonical.Surface.m0425 :
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
(∀ (_v18 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v5)),
(∀ (_v19 : (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v6)),
(let _v20 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation _v0);
(let _v21 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat))));
(let _v22 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v21 _v3) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat))));
(let _v23 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v0);
(∀ (_v24 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v8)),
(∀ (_v25 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v22 _v8) _v23)),
(∀ (_v26 : (∀ (_v26 : (@Nat)),
(∀ (_v27 : (@LE.le.{0} (@Nat) (@instLENat) _v7 _v26)),
(∀ (_v28 : (@LT.lt.{0} (@Nat) (@instLTNat) _v26 _v1)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v11 _v26) (@Option.some.{0} (@Bool) (@_v9 (@Fin.mk _v1 _v26 _v28)))))))),
(∀ (_v27 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v11 _v1) (@Option.none.{0} (@Bool)))),
(∀ (_v28 : (∀ (_v28 : (@Nat)),
(∀ (_v29 : (@LT.lt.{0} (@Nat) (@instLTNat) _v1 _v28)),
(∀ (_v30 : (@LT.lt.{0} (@Nat) (@instLTNat) _v28 _v21)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v11 _v28) (@Option.some.{0} (@Bool) (@Bool.false))))))),
(∀ (_v29 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v11 _v21) (@Option.none.{0} (@Bool)))),
(∀ (_v30 : (∀ (_v30 : (@Fin _v3)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v11 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v22 (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Fin.val _v3 _v30))) (@Option.some.{0} (@Bool) (@_v10 _v30))))),
(∀ (_v31 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v11 _v22) (@Option.none.{0} (@Bool)))),
(∀ (_v32 : (∀ (_v32 : (@Nat)),
(∀ (_v33 : (@LT.lt.{0} (@Nat) (@instLTNat) _v22 _v32)),
(∀ (_v34 : (@LE.le.{0} (@Nat) (@instLENat) _v32 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v22 _v8))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v11 _v32) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v33 : (∀ (_v33 : (@Nat)),
(∀ (_v34 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v22 _v8) _v33)),
(∀ (_v35 : (@LT.lt.{0} (@Nat) (@instLTNat) _v33 _v23)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v11 _v33) (@Option.none.{0} (@Bool))))))),
(∀ (_v34 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v11 _v23) (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v35 : (@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter _v23 _v4 _v3 (@OfNat.ofNat.{0} (@Nat) (12 : Nat)
  (@instOfNatNat (12 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v20))),
(∀ (_v36 : (@LT.lt.{0} (@Nat) (@instLTNat) _v22 (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v20))),
(let _v37 : (∀ (_v37 : (@Nat)),
(@Nat)) := (@SerializedBody.delimiter _v23 _v4 _v3);
(let _v38 : (∀ (_v38 : (@Nat)),
(@Option.{0} (@Bool))) := (@SerializedBody.image _v11 _v23 _v4 _v3 _v5 _v6 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHSub.{0} (@Nat) (@instSubNat)) _v1 (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) _v7 _v1)) (@OfNat.ofNat.{0} (@Nat)
  (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v6 _v5);
(let _v39 : (∀ (_v39 : (@Nat)),
(@Option.{0} (@Bool))) := (fun (_v39 : (@Nat)) =>
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) _v39 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v37 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@instDecidableEqNat _v39 (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v37 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Option.some.{0} (@Bool) (@Bool.true)) (@ite.{(0 + 1)}
  (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) _v39 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@_v37 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) _v5)) (@instDecidableEqNat _v39
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v37 (@OfNat.ofNat.{0} (@Nat) (6 :
  Nat) (@instOfNatNat (6 : Nat)))) _v5)) (@Option.some.{0} (@Bool) (@Bool.false)) (@_v38 _v39))));
(let _v40 : (∀ (_v40 : (@Nat)),
(@Option.{0} (@Bool))) := (fun (_v40 : (@Nat)) =>
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@Eq.{(0 + 1)} (@Nat) _v40 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v7 (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))) (@LT.lt.{0}
  (@Nat) (@instLTNat) _v40 _v1)) (@instDecidableAnd (@Eq.{(0 + 1)} (@Nat) _v40 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v7 (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))) (@LT.lt.{0}
  (@Nat) (@instLTNat) _v40 _v1) (@instDecidableEqNat _v40 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v7 (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))) (@Nat.decLt _v40 _v1))
  (@Option.none.{0} (@Bool)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@_v37
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v40) (@LT.lt.{0} (@Nat) (@instLTNat) _v40 (@_v37
  (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat)
  (@_v37 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v40) (@LT.lt.{0} (@Nat) (@instLTNat) _v40 (@_v37
  (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))) (@Nat.decLt (@_v37 (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))) _v40) (@Nat.decLt _v40 (@_v37 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 :
  Nat)))))) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v40 (@_v37 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat))))) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (3
  : Nat) (@instOfNatNat (3 : Nat))))) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v40 (@_v37 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@HSub.hSub.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))))))
  (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@_v37 (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat)))) _v40) (@LT.lt.{0} (@Nat) (@instLTNat) _v40 (@_v37 (@OfNat.ofNat.{0} (@Nat) (12 : Nat)
  (@instOfNatNat (12 : Nat)))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@_v37 (@OfNat.ofNat.{0} (@Nat) (11 :
  Nat) (@instOfNatNat (11 : Nat)))) _v40) (@LT.lt.{0} (@Nat) (@instLTNat) _v40 (@_v37 (@OfNat.ofNat.{0} (@Nat) (12 : Nat)
  (@instOfNatNat (12 : Nat))))) (@Nat.decLt (@_v37 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) _v40)
  (@Nat.decLt _v40 (@_v37 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))))) (@Option.some.{0} (@Bool)
  (@Decidable.decide (@LE.le.{0} (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v40 (@_v37 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (3
  : Nat) (@instOfNatNat (3 : Nat)))) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v40 (@_v37 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (3
  : Nat) (@instOfNatNat (3 : Nat)))))) (@_v39 _v40)))));
(let _v41 : (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))) := (@ite.{(0 + 1)} (@Fin
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))) (@Eq.{(0 + 1)} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.padRead _v1 _v9 _v7) (@Bool.true)) (@instDecidableEqBool
  (@Pnp4.Frontier.ContractExpansion.padRead _v1 _v9 _v7) (@Bool.true)) (@ite.{(0 + 1)} (@Fin (@OfNat.ofNat.{0} (@Nat) (9 :
  Nat) (@instOfNatNat (9 : Nat)))) (@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead _v1 _v9
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v7 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@Bool.true)) (@instDecidableEqBool (@Pnp4.Frontier.ContractExpansion.padRead _v1 _v9
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v7 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@Bool.true)) (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9
  : Nat)))) (6 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@Nat.instNeZeroSucc
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))) (6 : Nat))) (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0}
  (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))) (5 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat
  (9 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))) (5 : Nat)))) (@ite.{(0 +
  1)} (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))) (@Eq.{(0 + 1)} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.padRead _v1 _v9 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v7 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Bool.true)) (@instDecidableEqBool
  (@Pnp4.Frontier.ContractExpansion.padRead _v1 _v9 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v7 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Bool.true)) (@OfNat.ofNat.{0} (@Fin
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))) (4 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (9 :
  Nat) (@instOfNatNat (9 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))) (4 :
  Nat))) (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))) (3 : Nat) (@Fin.instOfNat
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (8 : Nat)
  (@instOfNatNat (8 : Nat)))) (3 : Nat)))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v42 : (@Nat)) =>
(@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@_v37 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v20)) (fun (_v43 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v37 (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v20))) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v42 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (1073741824 : Nat) (@instOfNatNat (1073741824 : Nat))) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))) (@And (@Eq.{(0 + 1)}
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v0
  _v20) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v20 _v42
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v0 _v20
  (@SerializedBody.entry (@SerializedBody.sourceMode _v1 _v9 _v7)) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v0
  _v20) _v22 _v36) (fun (_v44 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v20))) =>
(@SerializedBody.prepared _v11 _v1 _v7 _v23 _v4 _v3 _v5 _v6 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v20)
  _v44))))) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v0 _v20 (@SerializedBodyRefinement.getExit _v41 (@Pnp4.Frontier.ContractExpansion.padRead
  _v1 _v9 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v7 (@OfNat.ofNat.{0} (@Nat) (2
  : Nat) (@instOfNatNat (2 : Nat))))) (@SerializedBody.sourceMode _v1 _v9 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v7 (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v20) (@_v37 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  _v43) (fun (_v44 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v20))) =>
(@_v40 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v20) _v44))))) (∀ (_v44 : (@Nat)),
(∀ (_v45 : (@LE.le.{0} (@Nat) (@instLENat) _v44 _v42)),
(@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v0 _v20
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v0 _v20 _v44
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v0 _v20
  (@SerializedBody.entry (@SerializedBody.sourceMode _v1 _v9 _v7)) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v0
  _v20) _v22 _v36) (fun (_v46 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v20))) =>
(@SerializedBody.prepared _v11 _v1 _v7 _v23 _v4 _v3 _v5 _v6 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v20)
  _v46)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @SerializedPositiveBody.initialized_node

-- Independent literal expected type for SerializedPositiveBody.open_node.
noncomputable def PartACanonical.Types.p0700 :
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
(∀ (_v11 : (@Nat)),
(∀ (_v12 : (@Nat)),
(∀ (_v13 : (@Nat)),
(∀ (_v14 : (@Nat)),
(∀ (_v15 : (@Nat)),
(∀ (_v16 : (∀ (_v16 : (@Fin _v2)),
(@Bool))),
(∀ (_v17 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v11)),
(∀ (_v18 : (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v11 _v12) _v7)),
(∀ (_v19 : (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v9)),
(∀ (_v20 : (@LE.le.{0} (@Nat) (@instLENat) _v9 _v7)),
(∀ (_v21 : (@LT.lt.{0} (@Nat) (@instLTNat) _v2 _v3)),
(∀ (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v4)),
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v5)),
(∀ (_v24 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v4 _v5) _v6)),
(∀ (_v25 : (@Eq.{(0 + 1)} (@Nat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))))),
(∀ (_v26 : (∀ (_v26 : (@Nat)),
(∀ (_v27 : (@LT.lt.{0} (@Nat) (@instLTNat) _v26 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 _v26) (@_v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v26 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))))),
(∀ (_v27 : (∀ (_v27 : (@Nat)),
(∀ (_v28 : (@Nat)),
(∀ (_v29 : (@LE.le.{0} (@Nat) (@instLENat) _v27 _v28)),
(∀ (_v30 : (@LE.le.{0} (@Nat) (@instLENat) _v28 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@LE.le.{0} (@Nat) (@instLENat) (@_v0 _v27) (@_v0 _v28))))))),
(∀ (_v28 : (∀ (_v28 : (@Nat)),
(∀ (_v29 : (@LE.le.{0} (@Nat) (@instLENat) _v28 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 (@_v0 _v28)) (@Option.none.{0} (@Bool)))))),
(∀ (_v29 : (∀ (_v29 : (@Nat)),
(∀ (_v30 : (@Nat)),
(∀ (_v31 : (@LT.lt.{0} (@Nat) (@instLTNat) _v29 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(∀ (_v32 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 _v29) _v30)),
(∀ (_v33 : (@LT.lt.{0} (@Nat) (@instLTNat) _v30 (@_v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v29 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))),
(@Exists.{(0 + 1)} (@Bool) (fun (_v34 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v30) (@Option.some.{0} (@Bool) _v34)))))))))),
(∀ (_v30 : (@Eq.{(0 + 1)} (@Nat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@_v0 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v7) (@OfNat.ofNat.{0} (@Nat)
  (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v31 : (@Eq.{(0 + 1)} (@Nat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@_v0 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) _v7) (@OfNat.ofNat.{0} (@Nat)
  (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v32 : (@Eq.{(0 + 1)} (@Nat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@_v0 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) _v7) (@OfNat.ofNat.{0} (@Nat)
  (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v33 : (@Eq.{(0 + 1)} (@Nat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v0 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) _v7)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v34 : (∀ (_v34 : (@Nat)),
(∀ (_v35 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) _v34)),
(∀ (_v36 : (@LT.lt.{0} (@Nat) (@instLTNat) _v34 (@_v0 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v34) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat)
  (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v34 (@_v0
  (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))) _v11) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v34 (@_v0 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))
  _v11)))))))),
(∀ (_v35 : (∀ (_v35 : (@Nat)),
(∀ (_v36 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) _v35)),
(∀ (_v37 : (@LT.lt.{0} (@Nat) (@instLTNat) _v35 (@_v0 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v35) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat)
  (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v35 (@_v0
  (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))) _v12) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v35 (@_v0 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))
  _v12)))))))),
(∀ (_v36 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v2) (@Option.none.{0} (@Bool)))),
(∀ (_v37 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v3) (@Option.none.{0} (@Bool)))),
(∀ (_v38 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v4) (@Option.none.{0} (@Bool)))),
(∀ (_v39 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v6) (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v40 : (∀ (_v40 : (@Nat)),
(∀ (_v41 : (@LT.lt.{0} (@Nat) (@instLTNat) _v2 _v40)),
(∀ (_v42 : (@LT.lt.{0} (@Nat) (@instLTNat) _v40 _v3)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v43 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v40) (@Option.some.{0} (@Bool) _v43)))))))),
(∀ (_v41 : (∀ (_v41 : (@Nat)),
(∀ (_v42 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v41)),
(∀ (_v43 : (@LT.lt.{0} (@Nat) (@instLTNat) _v41 _v4)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v44 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v41) (@Option.some.{0} (@Bool) _v44)))))))),
(∀ (_v42 : (∀ (_v42 : (@Nat)),
(∀ (_v43 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 _v42)),
(∀ (_v44 : (@LE.le.{0} (@Nat) (@instLENat) _v42 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v4 _v5))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v42) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v43 : (∀ (_v43 : (@Nat)),
(∀ (_v44 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v4 _v5) _v43)),
(∀ (_v45 : (@LT.lt.{0} (@Nat) (@instLTNat) _v43 _v6)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v43) (@Option.none.{0} (@Bool))))))),
(∀ (_v44 : (∀ (_v44 : (@Nat)),
(∀ (_v45 : (@LE.le.{0} (@Nat) (@instLENat) _v8 _v44)),
(∀ (_v46 : (@LT.lt.{0} (@Nat) (@instLTNat) _v44 _v2)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v44) (@Option.some.{0} (@Bool) (@_v16 (@Fin.mk _v2 _v44 _v46)))))))),
(∀ (_v45 : (@LE.le.{0} (@Nat) (@instLENat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))
  _v15)),
(∀ (_v46 : (@LT.lt.{0} (@Nat) (@instLTNat) _v15 (@Pnp3.Complexity.Uniform.V1.tapeLength _v13 _v14))),
(∀ (_v47 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 (@Pnp3.Complexity.Uniform.V1.tapeLength _v13 _v14))),
(∀ (_v48 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v13 _v14))),
(let _v49 : (∀ (_v49 : (∀ (_v49 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v50 : (@Nat)),
(∀ (_v51 : (@Nat)),
(@Option.{0} (@Bool))))) := (fun (_v49 : (∀ (_v49 : (@Nat)),
(@Option.{0} (@Bool)))) =>
(fun (_v50 : (@Nat)) =>
(fun (_v51 : (@Nat)) =>
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@Eq.{(0 + 1)} (@Nat) _v51 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v8 _v50)) (@LT.lt.{0} (@Nat) (@instLTNat) _v51 _v2)) (@instDecidableAnd (@Eq.{(0 +
  1)} (@Nat) _v51 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v8 _v50)) (@LT.lt.{0}
  (@Nat) (@instLTNat) _v51 _v2) (@instDecidableEqNat _v51 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v8 _v50)) (@Nat.decLt _v51 _v2)) (@Option.none.{0} (@Bool)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And
  (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v51) (@LT.lt.{0}
  (@Nat) (@instLTNat) _v51 (@_v0 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))) (@instDecidableAnd
  (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v51) (@LT.lt.{0}
  (@Nat) (@instLTNat) _v51 (@_v0 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))) (@Nat.decLt (@_v0
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v51) (@Nat.decLt _v51 (@_v0 (@OfNat.ofNat.{0} (@Nat) (5
  : Nat) (@instOfNatNat (5 : Nat)))))) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat) (@instLENat)
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v51 (@_v0 (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat))))) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v9
  _v50)) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v51 (@_v0
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHSub.{0} (@Nat) (@instSubNat)) _v9 _v50)))) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat)
  (@instLTNat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) _v51) (@LT.lt.{0} (@Nat)
  (@instLTNat) _v51 (@_v0 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))))) (@instDecidableAnd
  (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) _v51) (@LT.lt.{0}
  (@Nat) (@instLTNat) _v51 (@_v0 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))) (@Nat.decLt (@_v0
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) _v51) (@Nat.decLt _v51 (@_v0 (@OfNat.ofNat.{0} (@Nat)
  (12 : Nat) (@instOfNatNat (12 : Nat)))))) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat) (@instLENat)
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v51 (@_v0 (@OfNat.ofNat.{0} (@Nat) (11
  : Nat) (@instOfNatNat (11 : Nat))))) _v50) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v51 (@_v0 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))) _v50))) (@_v49 _v51)))))));
(let _v50 : (∀ (_v50 : (@Nat)),
(@Option.{0} (@Bool))) := (fun (_v50 : (@Nat)) =>
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) _v50 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@_v0 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) _v12) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@instDecidableEqNat _v50 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v0 (@OfNat.ofNat.{0}
  (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) _v12) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))
  (@Option.some.{0} (@Bool) (@Bool.true)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) _v50 (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v0 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat
  (6 : Nat)))) _v11)) (@instDecidableEqNat _v50 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@_v0 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) _v11)) (@Option.some.{0} (@Bool)
  (@Bool.false)) (@_v1 _v50))));
(let _v51 : (@Bool) := (@Pnp4.Frontier.ContractExpansion.padRead _v2 _v16 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v8 _v10));
(let _v52 : (@Bool) := (@Pnp4.Frontier.ContractExpansion.padRead _v2 _v16 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v8 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  _v10 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))));
(let _v53 : (@Bool) := (@Pnp4.Frontier.ContractExpansion.padRead _v2 _v16 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v8 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  _v10 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))));
(let _v54 : (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))) := (@ite.{(0 + 1)} (@Fin
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))) (@Eq.{(0 + 1)} (@Bool) _v51 (@Bool.true))
  (@instDecidableEqBool _v51 (@Bool.true)) (@ite.{(0 + 1)} (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 :
  Nat)))) (@Eq.{(0 + 1)} (@Bool) _v52 (@Bool.true)) (@instDecidableEqBool _v52 (@Bool.true)) (@OfNat.ofNat.{0} (@Fin
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))) (6 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (9 :
  Nat) (@instOfNatNat (9 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))) (6 :
  Nat))) (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))) (5 : Nat) (@Fin.instOfNat
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (8 : Nat)
  (@instOfNatNat (8 : Nat)))) (5 : Nat)))) (@ite.{(0 + 1)} (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 :
  Nat)))) (@Eq.{(0 + 1)} (@Bool) _v52 (@Bool.true)) (@instDecidableEqBool _v52 (@Bool.true)) (@OfNat.ofNat.{0} (@Fin
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))) (4 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (9 :
  Nat) (@instOfNatNat (9 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))) (4 :
  Nat))) (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))) (3 : Nat) (@Fin.instOfNat
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (8 : Nat)
  (@instOfNatNat (8 : Nat)))) (3 : Nat)))));
(let _v55 : (@Pnp3.Complexity.Uniform.V1.Config (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v13
  _v14) := (@Pnp3.Complexity.Uniform.V1.Config.mk (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v13
  _v14 (@SerializedBody.entry (@SerializedBody.sourceMode _v2 _v16 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v8 _v10))) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v13 _v14) _v4 _v47)
  (fun (_v55 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v13 _v14))) =>
(@_v49 _v1 _v10 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v13 _v14) _v55))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v56 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v56 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (512 : Nat) (@instOfNatNat (512 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v15 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@And
  (@Eq.{(0 + 1)} (@Nat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HSub.hSub.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v11 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v12 (@OfNat.ofNat.{0} (@Nat) (1
  : Nat) (@instOfNatNat (1 : Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v11
  _v12)) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v13 _v14) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v13 _v14
  _v56 _v55) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v13 _v14 (@SerializedBodyRefinement.getExit _v54 _v53 (@SerializedBody.sourceMode _v2 _v16
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v8 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))))))
  (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v13 _v14) (@_v0 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat)))) _v48) (fun (_v57 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v13 _v14))) =>
(@_v49 _v50 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v13 _v14) _v57))))) (∀
  (_v57 : (@Nat)),
(∀ (_v58 : (@LE.le.{0} (@Nat) (@instLENat) _v57 _v56)),
(@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v13 _v14
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v13 _v14 _v57
  _v55))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @SerializedPositiveBody.open_node

-- Complete literal proposition for SerializedPositiveBody.open_node; original proof reused.
theorem PartACanonical.Surface.m0426 :
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
(∀ (_v11 : (@Nat)),
(∀ (_v12 : (@Nat)),
(∀ (_v13 : (@Nat)),
(∀ (_v14 : (@Nat)),
(∀ (_v15 : (@Nat)),
(∀ (_v16 : (∀ (_v16 : (@Fin _v2)),
(@Bool))),
(∀ (_v17 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v11)),
(∀ (_v18 : (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v11 _v12) _v7)),
(∀ (_v19 : (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v9)),
(∀ (_v20 : (@LE.le.{0} (@Nat) (@instLENat) _v9 _v7)),
(∀ (_v21 : (@LT.lt.{0} (@Nat) (@instLTNat) _v2 _v3)),
(∀ (_v22 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v4)),
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v5)),
(∀ (_v24 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v4 _v5) _v6)),
(∀ (_v25 : (@Eq.{(0 + 1)} (@Nat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))))),
(∀ (_v26 : (∀ (_v26 : (@Nat)),
(∀ (_v27 : (@LT.lt.{0} (@Nat) (@instLTNat) _v26 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 _v26) (@_v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v26 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))))),
(∀ (_v27 : (∀ (_v27 : (@Nat)),
(∀ (_v28 : (@Nat)),
(∀ (_v29 : (@LE.le.{0} (@Nat) (@instLENat) _v27 _v28)),
(∀ (_v30 : (@LE.le.{0} (@Nat) (@instLENat) _v28 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@LE.le.{0} (@Nat) (@instLENat) (@_v0 _v27) (@_v0 _v28))))))),
(∀ (_v28 : (∀ (_v28 : (@Nat)),
(∀ (_v29 : (@LE.le.{0} (@Nat) (@instLENat) _v28 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 (@_v0 _v28)) (@Option.none.{0} (@Bool)))))),
(∀ (_v29 : (∀ (_v29 : (@Nat)),
(∀ (_v30 : (@Nat)),
(∀ (_v31 : (@LT.lt.{0} (@Nat) (@instLTNat) _v29 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(∀ (_v32 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 _v29) _v30)),
(∀ (_v33 : (@LT.lt.{0} (@Nat) (@instLTNat) _v30 (@_v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v29 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))),
(@Exists.{(0 + 1)} (@Bool) (fun (_v34 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v30) (@Option.some.{0} (@Bool) _v34)))))))))),
(∀ (_v30 : (@Eq.{(0 + 1)} (@Nat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@_v0 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v7) (@OfNat.ofNat.{0} (@Nat)
  (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v31 : (@Eq.{(0 + 1)} (@Nat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@_v0 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) _v7) (@OfNat.ofNat.{0} (@Nat)
  (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v32 : (@Eq.{(0 + 1)} (@Nat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@_v0 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) _v7) (@OfNat.ofNat.{0} (@Nat)
  (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v33 : (@Eq.{(0 + 1)} (@Nat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v0 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) _v7)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v34 : (∀ (_v34 : (@Nat)),
(∀ (_v35 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) _v34)),
(∀ (_v36 : (@LT.lt.{0} (@Nat) (@instLTNat) _v34 (@_v0 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v34) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat)
  (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v34 (@_v0
  (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))) _v11) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v34 (@_v0 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))
  _v11)))))))),
(∀ (_v35 : (∀ (_v35 : (@Nat)),
(∀ (_v36 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) _v35)),
(∀ (_v37 : (@LT.lt.{0} (@Nat) (@instLTNat) _v35 (@_v0 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v35) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat)
  (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v35 (@_v0
  (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))) _v12) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v35 (@_v0 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))
  _v12)))))))),
(∀ (_v36 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v2) (@Option.none.{0} (@Bool)))),
(∀ (_v37 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v3) (@Option.none.{0} (@Bool)))),
(∀ (_v38 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v4) (@Option.none.{0} (@Bool)))),
(∀ (_v39 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v6) (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v40 : (∀ (_v40 : (@Nat)),
(∀ (_v41 : (@LT.lt.{0} (@Nat) (@instLTNat) _v2 _v40)),
(∀ (_v42 : (@LT.lt.{0} (@Nat) (@instLTNat) _v40 _v3)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v43 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v40) (@Option.some.{0} (@Bool) _v43)))))))),
(∀ (_v41 : (∀ (_v41 : (@Nat)),
(∀ (_v42 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v41)),
(∀ (_v43 : (@LT.lt.{0} (@Nat) (@instLTNat) _v41 _v4)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v44 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v41) (@Option.some.{0} (@Bool) _v44)))))))),
(∀ (_v42 : (∀ (_v42 : (@Nat)),
(∀ (_v43 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 _v42)),
(∀ (_v44 : (@LE.le.{0} (@Nat) (@instLENat) _v42 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v4 _v5))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v42) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v43 : (∀ (_v43 : (@Nat)),
(∀ (_v44 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v4 _v5) _v43)),
(∀ (_v45 : (@LT.lt.{0} (@Nat) (@instLTNat) _v43 _v6)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v43) (@Option.none.{0} (@Bool))))))),
(∀ (_v44 : (∀ (_v44 : (@Nat)),
(∀ (_v45 : (@LE.le.{0} (@Nat) (@instLENat) _v8 _v44)),
(∀ (_v46 : (@LT.lt.{0} (@Nat) (@instLTNat) _v44 _v2)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v44) (@Option.some.{0} (@Bool) (@_v16 (@Fin.mk _v2 _v44 _v46)))))))),
(∀ (_v45 : (@LE.le.{0} (@Nat) (@instLENat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))
  _v15)),
(∀ (_v46 : (@LT.lt.{0} (@Nat) (@instLTNat) _v15 (@Pnp3.Complexity.Uniform.V1.tapeLength _v13 _v14))),
(∀ (_v47 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 (@Pnp3.Complexity.Uniform.V1.tapeLength _v13 _v14))),
(∀ (_v48 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v13 _v14))),
(let _v49 : (∀ (_v49 : (∀ (_v49 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v50 : (@Nat)),
(∀ (_v51 : (@Nat)),
(@Option.{0} (@Bool))))) := (fun (_v49 : (∀ (_v49 : (@Nat)),
(@Option.{0} (@Bool)))) =>
(fun (_v50 : (@Nat)) =>
(fun (_v51 : (@Nat)) =>
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@Eq.{(0 + 1)} (@Nat) _v51 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v8 _v50)) (@LT.lt.{0} (@Nat) (@instLTNat) _v51 _v2)) (@instDecidableAnd (@Eq.{(0 +
  1)} (@Nat) _v51 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v8 _v50)) (@LT.lt.{0}
  (@Nat) (@instLTNat) _v51 _v2) (@instDecidableEqNat _v51 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v8 _v50)) (@Nat.decLt _v51 _v2)) (@Option.none.{0} (@Bool)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And
  (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v51) (@LT.lt.{0}
  (@Nat) (@instLTNat) _v51 (@_v0 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))) (@instDecidableAnd
  (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v51) (@LT.lt.{0}
  (@Nat) (@instLTNat) _v51 (@_v0 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))) (@Nat.decLt (@_v0
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v51) (@Nat.decLt _v51 (@_v0 (@OfNat.ofNat.{0} (@Nat) (5
  : Nat) (@instOfNatNat (5 : Nat)))))) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat) (@instLENat)
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v51 (@_v0 (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat))))) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v9
  _v50)) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v51 (@_v0
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHSub.{0} (@Nat) (@instSubNat)) _v9 _v50)))) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat)
  (@instLTNat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) _v51) (@LT.lt.{0} (@Nat)
  (@instLTNat) _v51 (@_v0 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))))) (@instDecidableAnd
  (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) _v51) (@LT.lt.{0}
  (@Nat) (@instLTNat) _v51 (@_v0 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))) (@Nat.decLt (@_v0
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) _v51) (@Nat.decLt _v51 (@_v0 (@OfNat.ofNat.{0} (@Nat)
  (12 : Nat) (@instOfNatNat (12 : Nat)))))) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat) (@instLENat)
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v51 (@_v0 (@OfNat.ofNat.{0} (@Nat) (11
  : Nat) (@instOfNatNat (11 : Nat))))) _v50) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v51 (@_v0 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))) _v50))) (@_v49 _v51)))))));
(let _v50 : (∀ (_v50 : (@Nat)),
(@Option.{0} (@Bool))) := (fun (_v50 : (@Nat)) =>
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) _v50 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@_v0 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) _v12) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@instDecidableEqNat _v50 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v0 (@OfNat.ofNat.{0}
  (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) _v12) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))
  (@Option.some.{0} (@Bool) (@Bool.true)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)} (@Nat) _v50 (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v0 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat
  (6 : Nat)))) _v11)) (@instDecidableEqNat _v50 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@_v0 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) _v11)) (@Option.some.{0} (@Bool)
  (@Bool.false)) (@_v1 _v50))));
(let _v51 : (@Bool) := (@Pnp4.Frontier.ContractExpansion.padRead _v2 _v16 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v8 _v10));
(let _v52 : (@Bool) := (@Pnp4.Frontier.ContractExpansion.padRead _v2 _v16 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v8 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  _v10 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))));
(let _v53 : (@Bool) := (@Pnp4.Frontier.ContractExpansion.padRead _v2 _v16 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v8 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  _v10 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))));
(let _v54 : (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))) := (@ite.{(0 + 1)} (@Fin
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))) (@Eq.{(0 + 1)} (@Bool) _v51 (@Bool.true))
  (@instDecidableEqBool _v51 (@Bool.true)) (@ite.{(0 + 1)} (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 :
  Nat)))) (@Eq.{(0 + 1)} (@Bool) _v52 (@Bool.true)) (@instDecidableEqBool _v52 (@Bool.true)) (@OfNat.ofNat.{0} (@Fin
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))) (6 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (9 :
  Nat) (@instOfNatNat (9 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))) (6 :
  Nat))) (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))) (5 : Nat) (@Fin.instOfNat
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (8 : Nat)
  (@instOfNatNat (8 : Nat)))) (5 : Nat)))) (@ite.{(0 + 1)} (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 :
  Nat)))) (@Eq.{(0 + 1)} (@Bool) _v52 (@Bool.true)) (@instDecidableEqBool _v52 (@Bool.true)) (@OfNat.ofNat.{0} (@Fin
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))) (4 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (9 :
  Nat) (@instOfNatNat (9 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))) (4 :
  Nat))) (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))) (3 : Nat) (@Fin.instOfNat
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (8 : Nat)
  (@instOfNatNat (8 : Nat)))) (3 : Nat)))));
(let _v55 : (@Pnp3.Complexity.Uniform.V1.Config (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v13
  _v14) := (@Pnp3.Complexity.Uniform.V1.Config.mk (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v13
  _v14 (@SerializedBody.entry (@SerializedBody.sourceMode _v2 _v16 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v8 _v10))) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v13 _v14) _v4 _v47)
  (fun (_v55 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v13 _v14))) =>
(@_v49 _v1 _v10 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v13 _v14) _v55))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v56 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v56 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (512 : Nat) (@instOfNatNat (512 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v15 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@And
  (@Eq.{(0 + 1)} (@Nat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HSub.hSub.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v11 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v12 (@OfNat.ofNat.{0} (@Nat) (1
  : Nat) (@instOfNatNat (1 : Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v11
  _v12)) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v13 _v14) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v13 _v14
  _v56 _v55) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v13 _v14 (@SerializedBodyRefinement.getExit _v54 _v53 (@SerializedBody.sourceMode _v2 _v16
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v8 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))))))
  (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v13 _v14) (@_v0 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat)))) _v48) (fun (_v57 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v13 _v14))) =>
(@_v49 _v50 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v13 _v14) _v57))))) (∀
  (_v57 : (@Nat)),
(∀ (_v58 : (@LE.le.{0} (@Nat) (@instLENat) _v57 _v56)),
(@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v13 _v14
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v13 _v14 _v57
  _v55))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @SerializedPositiveBody.open_node

-- Independent literal expected type for SerializedPositiveBody.positive_reader.
noncomputable def PartACanonical.Types.p0701 :
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
(∀ (_v14 : (@Nat)),
(∀ (_v15 : (∀ (_v15 : (@Fin _v3)),
(@Bool))),
(∀ (_v16 : (@LT.lt.{0} (@Nat) (@instLTNat) _v11 _v10)),
(∀ (_v17 : (@LE.le.{0} (@Nat) (@instLENat) _v10 _v8)),
(∀ (_v18 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v4)),
(∀ (_v19 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 _v5)),
(∀ (_v20 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v6)),
(∀ (_v21 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v5 _v6) _v7)),
(∀ (_v22 : (@Eq.{(0 + 1)} (@Nat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v7 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))))),
(∀ (_v23 : (∀ (_v23 : (@Nat)),
(∀ (_v24 : (@LT.lt.{0} (@Nat) (@instLTNat) _v23 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 _v23) (@_v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v23 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))))),
(∀ (_v24 : (∀ (_v24 : (@Nat)),
(∀ (_v25 : (@Nat)),
(∀ (_v26 : (@LE.le.{0} (@Nat) (@instLENat) _v24 _v25)),
(∀ (_v27 : (@LE.le.{0} (@Nat) (@instLENat) _v25 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@LE.le.{0} (@Nat) (@instLENat) (@_v1 _v24) (@_v1 _v25))))))),
(∀ (_v25 : (∀ (_v25 : (@Nat)),
(∀ (_v26 : (@LE.le.{0} (@Nat) (@instLENat) _v25 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 (@_v1 _v25)) (@Option.none.{0} (@Bool)))))),
(∀ (_v26 : (∀ (_v26 : (@Nat)),
(∀ (_v27 : (@Nat)),
(∀ (_v28 : (@LT.lt.{0} (@Nat) (@instLTNat) _v26 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(∀ (_v29 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 _v26) _v27)),
(∀ (_v30 : (@LT.lt.{0} (@Nat) (@instLTNat) _v27 (@_v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v26 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))),
(@Exists.{(0 + 1)} (@Bool) (fun (_v31 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v27) (@Option.some.{0} (@Bool) _v31)))))))))),
(∀ (_v27 : (@Eq.{(0 + 1)} (@Nat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@_v1 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v8) (@OfNat.ofNat.{0} (@Nat)
  (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v28 : (@Eq.{(0 + 1)} (@Nat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v1 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) _v8)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v29 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v3) (@Option.none.{0} (@Bool)))),
(∀ (_v30 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v4) (@Option.none.{0} (@Bool)))),
(∀ (_v31 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v5) (@Option.none.{0} (@Bool)))),
(∀ (_v32 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v7) (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v33 : (∀ (_v33 : (@Nat)),
(∀ (_v34 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v33)),
(∀ (_v35 : (@LT.lt.{0} (@Nat) (@instLTNat) _v33 _v4)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v36 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v33) (@Option.some.{0} (@Bool) _v36)))))))),
(∀ (_v34 : (∀ (_v34 : (@Nat)),
(∀ (_v35 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 _v34)),
(∀ (_v36 : (@LT.lt.{0} (@Nat) (@instLTNat) _v34 _v5)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v37 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v34) (@Option.some.{0} (@Bool) _v37)))))))),
(∀ (_v35 : (∀ (_v35 : (@Nat)),
(∀ (_v36 : (@LT.lt.{0} (@Nat) (@instLTNat) _v5 _v35)),
(∀ (_v37 : (@LE.le.{0} (@Nat) (@instLENat) _v35 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v5 _v6))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v35) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v36 : (∀ (_v36 : (@Nat)),
(∀ (_v37 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v5 _v6) _v36)),
(∀ (_v38 : (@LT.lt.{0} (@Nat) (@instLTNat) _v36 _v7)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v36) (@Option.none.{0} (@Bool))))))),
(∀ (_v37 : (∀ (_v37 : (@Nat)),
(∀ (_v38 : (@LE.le.{0} (@Nat) (@instLENat) _v9 _v37)),
(∀ (_v39 : (@LT.lt.{0} (@Nat) (@instLTNat) _v37 _v3)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v37) (@Option.some.{0} (@Bool) (@_v15 (@Fin.mk _v3 _v37 _v39)))))))),
(∀ (_v38 : (@LE.le.{0} (@Nat) (@instLENat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))
  _v14)),
(∀ (_v39 : (@LT.lt.{0} (@Nat) (@instLTNat) _v14 (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13))),
(∀ (_v40 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13))),
(let _v41 : (∀ (_v41 : (@Nat)),
(∀ (_v42 : (@Nat)),
(@Option.{0} (@Bool)))) := (fun (_v41 : (@Nat)) =>
(fun (_v42 : (@Nat)) =>
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@Eq.{(0 + 1)} (@Nat) _v42 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v9 _v41)) (@LT.lt.{0} (@Nat) (@instLTNat) _v42 _v3)) (@instDecidableAnd (@Eq.{(0 +
  1)} (@Nat) _v42 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v9 _v41)) (@LT.lt.{0}
  (@Nat) (@instLTNat) _v42 _v3) (@instDecidableEqNat _v42 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v9 _v41)) (@Nat.decLt _v42 _v3)) (@Option.none.{0} (@Bool)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And
  (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v42) (@LT.lt.{0}
  (@Nat) (@instLTNat) _v42 (@_v1 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))) (@instDecidableAnd
  (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v42) (@LT.lt.{0}
  (@Nat) (@instLTNat) _v42 (@_v1 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))) (@Nat.decLt (@_v1
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v42) (@Nat.decLt _v42 (@_v1 (@OfNat.ofNat.{0} (@Nat) (5
  : Nat) (@instOfNatNat (5 : Nat)))))) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat) (@instLENat)
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v42 (@_v1 (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat))))) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v10
  _v41)) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v42 (@_v1
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHSub.{0} (@Nat) (@instSubNat)) _v10 _v41)))) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat)
  (@instLTNat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) _v42) (@LT.lt.{0} (@Nat)
  (@instLTNat) _v42 (@_v1 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))))) (@instDecidableAnd
  (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) _v42) (@LT.lt.{0}
  (@Nat) (@instLTNat) _v42 (@_v1 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))) (@Nat.decLt (@_v1
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) _v42) (@Nat.decLt _v42 (@_v1 (@OfNat.ofNat.{0} (@Nat)
  (12 : Nat) (@instOfNatNat (12 : Nat)))))) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat) (@instLENat)
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v42 (@_v1 (@OfNat.ofNat.{0} (@Nat) (11
  : Nat) (@instOfNatNat (11 : Nat))))) _v41) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v42 (@_v1 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))) _v41))) (@_v2 _v42))))));
(let _v42 : (@Pnp3.Complexity.Uniform.V1.Config (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v12
  _v13) := (@Pnp3.Complexity.Uniform.V1.Config.mk (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v12
  _v13 (@SerializedBodyRefinement.getEntry _v0 (@SerializedBody.sourceMode _v3 _v15 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v9 _v11))) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13)
  (@_v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v40) (fun (_v42 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13))) =>
(@_v41 _v11 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13) _v42))));
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@GetElem?.getElem?.{0, 0, 0} (@List.{0} (@Bool)) (@Nat) (@Bool) (fun (_v43 :
  (@List.{0} (@Bool))) =>
(fun (_v44 : (@Nat)) =>
(@LT.lt.{0} (@Nat) (@instLTNat) _v44 (@List.length.{0} (@Bool) _v43)))) (@List.instGetElem?NatLtLength.{0} (@Bool))
  (@SerializedBody.window _v3 _v15 _v9 _v10) _v11) (@Option.some.{0} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead _v3
  _v15 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v9 _v11)))) (@Exists.{(0 + 1)}
  (@Nat) (fun (_v43 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v43 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@And
  (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v12 _v13) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v12 _v13
  _v43 _v42) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v12 _v13 (@SerializedBodyRefinement.getExit _v0 (@Pnp4.Frontier.ContractExpansion.padRead
  _v3 _v15 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v9 _v11))
  (@SerializedBody.sourceMode _v3 _v15 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v9
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))))) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13) (@_v1 (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v40) (fun (_v44 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v12
  _v13))) =>
(@_v41 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 (@OfNat.ofNat.{0} (@Nat) (1
  : Nat) (@instOfNatNat (1 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13) _v44))))) (∀ (_v44 :
  (@Nat)),
(∀ (_v45 : (@LE.le.{0} (@Nat) (@instLENat) _v44 _v43)),
(@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v12 _v13
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v12 _v13 _v44
  _v42)))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @SerializedPositiveBody.positive_reader

-- Complete literal proposition for SerializedPositiveBody.positive_reader; original proof reused.
theorem PartACanonical.Surface.m0427 :
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
(∀ (_v14 : (@Nat)),
(∀ (_v15 : (∀ (_v15 : (@Fin _v3)),
(@Bool))),
(∀ (_v16 : (@LT.lt.{0} (@Nat) (@instLTNat) _v11 _v10)),
(∀ (_v17 : (@LE.le.{0} (@Nat) (@instLENat) _v10 _v8)),
(∀ (_v18 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v4)),
(∀ (_v19 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 _v5)),
(∀ (_v20 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v6)),
(∀ (_v21 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v5 _v6) _v7)),
(∀ (_v22 : (@Eq.{(0 + 1)} (@Nat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v7 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))))),
(∀ (_v23 : (∀ (_v23 : (@Nat)),
(∀ (_v24 : (@LT.lt.{0} (@Nat) (@instLTNat) _v23 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 _v23) (@_v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v23 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))))),
(∀ (_v24 : (∀ (_v24 : (@Nat)),
(∀ (_v25 : (@Nat)),
(∀ (_v26 : (@LE.le.{0} (@Nat) (@instLENat) _v24 _v25)),
(∀ (_v27 : (@LE.le.{0} (@Nat) (@instLENat) _v25 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@LE.le.{0} (@Nat) (@instLENat) (@_v1 _v24) (@_v1 _v25))))))),
(∀ (_v25 : (∀ (_v25 : (@Nat)),
(∀ (_v26 : (@LE.le.{0} (@Nat) (@instLENat) _v25 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 (@_v1 _v25)) (@Option.none.{0} (@Bool)))))),
(∀ (_v26 : (∀ (_v26 : (@Nat)),
(∀ (_v27 : (@Nat)),
(∀ (_v28 : (@LT.lt.{0} (@Nat) (@instLTNat) _v26 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(∀ (_v29 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 _v26) _v27)),
(∀ (_v30 : (@LT.lt.{0} (@Nat) (@instLTNat) _v27 (@_v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v26 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))),
(@Exists.{(0 + 1)} (@Bool) (fun (_v31 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v27) (@Option.some.{0} (@Bool) _v31)))))))))),
(∀ (_v27 : (@Eq.{(0 + 1)} (@Nat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@_v1 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v8) (@OfNat.ofNat.{0} (@Nat)
  (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v28 : (@Eq.{(0 + 1)} (@Nat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v1 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) _v8)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v29 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v3) (@Option.none.{0} (@Bool)))),
(∀ (_v30 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v4) (@Option.none.{0} (@Bool)))),
(∀ (_v31 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v5) (@Option.none.{0} (@Bool)))),
(∀ (_v32 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v7) (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v33 : (∀ (_v33 : (@Nat)),
(∀ (_v34 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v33)),
(∀ (_v35 : (@LT.lt.{0} (@Nat) (@instLTNat) _v33 _v4)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v36 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v33) (@Option.some.{0} (@Bool) _v36)))))))),
(∀ (_v34 : (∀ (_v34 : (@Nat)),
(∀ (_v35 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 _v34)),
(∀ (_v36 : (@LT.lt.{0} (@Nat) (@instLTNat) _v34 _v5)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v37 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v34) (@Option.some.{0} (@Bool) _v37)))))))),
(∀ (_v35 : (∀ (_v35 : (@Nat)),
(∀ (_v36 : (@LT.lt.{0} (@Nat) (@instLTNat) _v5 _v35)),
(∀ (_v37 : (@LE.le.{0} (@Nat) (@instLENat) _v35 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v5 _v6))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v35) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v36 : (∀ (_v36 : (@Nat)),
(∀ (_v37 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v5 _v6) _v36)),
(∀ (_v38 : (@LT.lt.{0} (@Nat) (@instLTNat) _v36 _v7)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v36) (@Option.none.{0} (@Bool))))))),
(∀ (_v37 : (∀ (_v37 : (@Nat)),
(∀ (_v38 : (@LE.le.{0} (@Nat) (@instLENat) _v9 _v37)),
(∀ (_v39 : (@LT.lt.{0} (@Nat) (@instLTNat) _v37 _v3)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v2 _v37) (@Option.some.{0} (@Bool) (@_v15 (@Fin.mk _v3 _v37 _v39)))))))),
(∀ (_v38 : (@LE.le.{0} (@Nat) (@instLENat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))
  _v14)),
(∀ (_v39 : (@LT.lt.{0} (@Nat) (@instLTNat) _v14 (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13))),
(∀ (_v40 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13))),
(let _v41 : (∀ (_v41 : (@Nat)),
(∀ (_v42 : (@Nat)),
(@Option.{0} (@Bool)))) := (fun (_v41 : (@Nat)) =>
(fun (_v42 : (@Nat)) =>
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@Eq.{(0 + 1)} (@Nat) _v42 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v9 _v41)) (@LT.lt.{0} (@Nat) (@instLTNat) _v42 _v3)) (@instDecidableAnd (@Eq.{(0 +
  1)} (@Nat) _v42 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v9 _v41)) (@LT.lt.{0}
  (@Nat) (@instLTNat) _v42 _v3) (@instDecidableEqNat _v42 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v9 _v41)) (@Nat.decLt _v42 _v3)) (@Option.none.{0} (@Bool)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And
  (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v42) (@LT.lt.{0}
  (@Nat) (@instLTNat) _v42 (@_v1 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))) (@instDecidableAnd
  (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v42) (@LT.lt.{0}
  (@Nat) (@instLTNat) _v42 (@_v1 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))) (@Nat.decLt (@_v1
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v42) (@Nat.decLt _v42 (@_v1 (@OfNat.ofNat.{0} (@Nat) (5
  : Nat) (@instOfNatNat (5 : Nat)))))) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat) (@instLENat)
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v42 (@_v1 (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat))))) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v10
  _v41)) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v42 (@_v1
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHSub.{0} (@Nat) (@instSubNat)) _v10 _v41)))) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat)
  (@instLTNat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) _v42) (@LT.lt.{0} (@Nat)
  (@instLTNat) _v42 (@_v1 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))))) (@instDecidableAnd
  (@LT.lt.{0} (@Nat) (@instLTNat) (@_v1 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) _v42) (@LT.lt.{0}
  (@Nat) (@instLTNat) _v42 (@_v1 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))) (@Nat.decLt (@_v1
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) _v42) (@Nat.decLt _v42 (@_v1 (@OfNat.ofNat.{0} (@Nat)
  (12 : Nat) (@instOfNatNat (12 : Nat)))))) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat) (@instLENat)
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v42 (@_v1 (@OfNat.ofNat.{0} (@Nat) (11
  : Nat) (@instOfNatNat (11 : Nat))))) _v41) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v42 (@_v1 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))) _v41))) (@_v2 _v42))))));
(let _v42 : (@Pnp3.Complexity.Uniform.V1.Config (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v12
  _v13) := (@Pnp3.Complexity.Uniform.V1.Config.mk (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v12
  _v13 (@SerializedBodyRefinement.getEntry _v0 (@SerializedBody.sourceMode _v3 _v15 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v9 _v11))) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13)
  (@_v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v40) (fun (_v42 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13))) =>
(@_v41 _v11 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13) _v42))));
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@GetElem?.getElem?.{0, 0, 0} (@List.{0} (@Bool)) (@Nat) (@Bool) (fun (_v43 :
  (@List.{0} (@Bool))) =>
(fun (_v44 : (@Nat)) =>
(@LT.lt.{0} (@Nat) (@instLTNat) _v44 (@List.length.{0} (@Bool) _v43)))) (@List.instGetElem?NatLtLength.{0} (@Bool))
  (@SerializedBody.window _v3 _v15 _v9 _v10) _v11) (@Option.some.{0} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead _v3
  _v15 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v9 _v11)))) (@Exists.{(0 + 1)}
  (@Nat) (fun (_v43 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v43 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@And
  (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v12 _v13) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v12 _v13
  _v43 _v42) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v12 _v13 (@SerializedBodyRefinement.getExit _v0 (@Pnp4.Frontier.ContractExpansion.padRead
  _v3 _v15 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v9 _v11))
  (@SerializedBody.sourceMode _v3 _v15 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v9
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))))) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13) (@_v1 (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v40) (fun (_v44 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v12
  _v13))) =>
(@_v41 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 (@OfNat.ofNat.{0} (@Nat) (1
  : Nat) (@instOfNatNat (1 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v12 _v13) _v44))))) (∀ (_v44 :
  (@Nat)),
(∀ (_v45 : (@LE.le.{0} (@Nat) (@instLENat) _v44 _v43)),
(@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v12 _v13
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v12 _v13 _v44
  _v42)))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @SerializedPositiveBody.positive_reader

-- Independent literal expected type for SerializedPositiveBody.tag_reader.
noncomputable def PartACanonical.Types.p0702 :
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
(∀ (_v11 : (@Nat)),
(∀ (_v12 : (@Nat)),
(∀ (_v13 : (@Nat)),
(∀ (_v14 : (∀ (_v14 : (@Fin _v2)),
(@Bool))),
(∀ (_v15 : (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v9)),
(∀ (_v16 : (@LE.le.{0} (@Nat) (@instLENat) _v9 _v7)),
(∀ (_v17 : (@LT.lt.{0} (@Nat) (@instLTNat) _v2 _v3)),
(∀ (_v18 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v4)),
(∀ (_v19 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v5)),
(∀ (_v20 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v4 _v5) _v6)),
(∀ (_v21 : (@Eq.{(0 + 1)} (@Nat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))))),
(∀ (_v22 : (∀ (_v22 : (@Nat)),
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) _v22 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 _v22) (@_v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v22 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))))),
(∀ (_v23 : (∀ (_v23 : (@Nat)),
(∀ (_v24 : (@Nat)),
(∀ (_v25 : (@LE.le.{0} (@Nat) (@instLENat) _v23 _v24)),
(∀ (_v26 : (@LE.le.{0} (@Nat) (@instLENat) _v24 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@LE.le.{0} (@Nat) (@instLENat) (@_v0 _v23) (@_v0 _v24))))))),
(∀ (_v24 : (∀ (_v24 : (@Nat)),
(∀ (_v25 : (@LE.le.{0} (@Nat) (@instLENat) _v24 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 (@_v0 _v24)) (@Option.none.{0} (@Bool)))))),
(∀ (_v25 : (∀ (_v25 : (@Nat)),
(∀ (_v26 : (@Nat)),
(∀ (_v27 : (@LT.lt.{0} (@Nat) (@instLTNat) _v25 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(∀ (_v28 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 _v25) _v26)),
(∀ (_v29 : (@LT.lt.{0} (@Nat) (@instLTNat) _v26 (@_v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v25 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))),
(@Exists.{(0 + 1)} (@Bool) (fun (_v30 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v26) (@Option.some.{0} (@Bool) _v30)))))))))),
(∀ (_v26 : (@Eq.{(0 + 1)} (@Nat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@_v0 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v7) (@OfNat.ofNat.{0} (@Nat)
  (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v27 : (@Eq.{(0 + 1)} (@Nat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v0 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) _v7)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v28 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v2) (@Option.none.{0} (@Bool)))),
(∀ (_v29 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v3) (@Option.none.{0} (@Bool)))),
(∀ (_v30 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v4) (@Option.none.{0} (@Bool)))),
(∀ (_v31 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v6) (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v32 : (∀ (_v32 : (@Nat)),
(∀ (_v33 : (@LT.lt.{0} (@Nat) (@instLTNat) _v2 _v32)),
(∀ (_v34 : (@LT.lt.{0} (@Nat) (@instLTNat) _v32 _v3)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v35 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v32) (@Option.some.{0} (@Bool) _v35)))))))),
(∀ (_v33 : (∀ (_v33 : (@Nat)),
(∀ (_v34 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v33)),
(∀ (_v35 : (@LT.lt.{0} (@Nat) (@instLTNat) _v33 _v4)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v36 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v33) (@Option.some.{0} (@Bool) _v36)))))))),
(∀ (_v34 : (∀ (_v34 : (@Nat)),
(∀ (_v35 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 _v34)),
(∀ (_v36 : (@LE.le.{0} (@Nat) (@instLENat) _v34 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v4 _v5))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v34) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v35 : (∀ (_v35 : (@Nat)),
(∀ (_v36 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v4 _v5) _v35)),
(∀ (_v37 : (@LT.lt.{0} (@Nat) (@instLTNat) _v35 _v6)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v35) (@Option.none.{0} (@Bool))))))),
(∀ (_v36 : (∀ (_v36 : (@Nat)),
(∀ (_v37 : (@LE.le.{0} (@Nat) (@instLENat) _v8 _v36)),
(∀ (_v38 : (@LT.lt.{0} (@Nat) (@instLTNat) _v36 _v2)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v36) (@Option.some.{0} (@Bool) (@_v14 (@Fin.mk _v2 _v36 _v38)))))))),
(∀ (_v37 : (@LE.le.{0} (@Nat) (@instLENat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))
  _v13)),
(∀ (_v38 : (@LT.lt.{0} (@Nat) (@instLTNat) _v13 (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12))),
(∀ (_v39 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12))),
(let _v40 : (∀ (_v40 : (@Nat)),
(∀ (_v41 : (@Nat)),
(@Option.{0} (@Bool)))) := (fun (_v40 : (@Nat)) =>
(fun (_v41 : (@Nat)) =>
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@Eq.{(0 + 1)} (@Nat) _v41 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v8 _v40)) (@LT.lt.{0} (@Nat) (@instLTNat) _v41 _v2)) (@instDecidableAnd (@Eq.{(0 +
  1)} (@Nat) _v41 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v8 _v40)) (@LT.lt.{0}
  (@Nat) (@instLTNat) _v41 _v2) (@instDecidableEqNat _v41 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v8 _v40)) (@Nat.decLt _v41 _v2)) (@Option.none.{0} (@Bool)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And
  (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v41) (@LT.lt.{0}
  (@Nat) (@instLTNat) _v41 (@_v0 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))) (@instDecidableAnd
  (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v41) (@LT.lt.{0}
  (@Nat) (@instLTNat) _v41 (@_v0 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))) (@Nat.decLt (@_v0
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v41) (@Nat.decLt _v41 (@_v0 (@OfNat.ofNat.{0} (@Nat) (5
  : Nat) (@instOfNatNat (5 : Nat)))))) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat) (@instLENat)
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v41 (@_v0 (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat))))) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v9
  _v40)) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v41 (@_v0
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHSub.{0} (@Nat) (@instSubNat)) _v9 _v40)))) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat)
  (@instLTNat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) _v41) (@LT.lt.{0} (@Nat)
  (@instLTNat) _v41 (@_v0 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))))) (@instDecidableAnd
  (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) _v41) (@LT.lt.{0}
  (@Nat) (@instLTNat) _v41 (@_v0 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))) (@Nat.decLt (@_v0
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) _v41) (@Nat.decLt _v41 (@_v0 (@OfNat.ofNat.{0} (@Nat)
  (12 : Nat) (@instOfNatNat (12 : Nat)))))) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat) (@instLENat)
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v41 (@_v0 (@OfNat.ofNat.{0} (@Nat) (11
  : Nat) (@instOfNatNat (11 : Nat))))) _v40) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v41 (@_v0 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))) _v40))) (@_v1 _v41))))));
(let _v41 : (@Bool) := (@Pnp4.Frontier.ContractExpansion.padRead _v2 _v14 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v8 _v10));
(let _v42 : (@Bool) := (@Pnp4.Frontier.ContractExpansion.padRead _v2 _v14 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v8 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  _v10 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))));
(let _v43 : (@Bool) := (@Pnp4.Frontier.ContractExpansion.padRead _v2 _v14 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v8 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  _v10 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))));
(let _v44 : (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))) := (@ite.{(0 + 1)} (@Fin
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))) (@Eq.{(0 + 1)} (@Bool) _v41 (@Bool.true))
  (@instDecidableEqBool _v41 (@Bool.true)) (@ite.{(0 + 1)} (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 :
  Nat)))) (@Eq.{(0 + 1)} (@Bool) _v42 (@Bool.true)) (@instDecidableEqBool _v42 (@Bool.true)) (@OfNat.ofNat.{0} (@Fin
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))) (6 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (9 :
  Nat) (@instOfNatNat (9 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))) (6 :
  Nat))) (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))) (5 : Nat) (@Fin.instOfNat
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (8 : Nat)
  (@instOfNatNat (8 : Nat)))) (5 : Nat)))) (@ite.{(0 + 1)} (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 :
  Nat)))) (@Eq.{(0 + 1)} (@Bool) _v42 (@Bool.true)) (@instDecidableEqBool _v42 (@Bool.true)) (@OfNat.ofNat.{0} (@Fin
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))) (4 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (9 :
  Nat) (@instOfNatNat (9 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))) (4 :
  Nat))) (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))) (3 : Nat) (@Fin.instOfNat
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (8 : Nat)
  (@instOfNatNat (8 : Nat)))) (3 : Nat)))));
(let _v45 : (@Pnp3.Complexity.Uniform.V1.Config (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v11
  _v12) := (@Pnp3.Complexity.Uniform.V1.Config.mk (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v11
  _v12 (@SerializedBodyRefinement.getEntry (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 :
  Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@Nat.instNeZeroSucc
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))) (0 : Nat))) (@SerializedBody.sourceMode _v2 _v14
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v8 _v10))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12) (@_v0 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  _v39) (fun (_v45 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12))) =>
(@_v40 _v10 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12) _v45))));
(@And (∀ (_v46 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@GetElem?.getElem?.{0, 0, 0} (@List.{0} (@Bool)) (@Nat) (@Bool) (fun (_v47 :
  (@List.{0} (@Bool))) =>
(fun (_v48 : (@Nat)) =>
(@LT.lt.{0} (@Nat) (@instLTNat) _v48 (@List.length.{0} (@Bool) _v47)))) (@List.instGetElem?NatLtLength.{0} (@Bool))
  (@SerializedBody.window _v2 _v14 _v8 _v9) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v10 (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v46))) (@Option.some.{0}
  (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead _v2 _v14 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v8 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v46))))))) (@Exists.{(0 + 1)} (@Nat) (fun (_v46 : (@Nat))
  =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v46 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (256 : Nat) (@instOfNatNat (256 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@And
  (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v11 _v12) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v11 _v12
  _v46 _v45) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v11 _v12 (@SerializedBodyRefinement.getExit _v44 _v43 (@SerializedBody.sourceMode _v2 _v14
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v8 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))))))
  (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12) (@_v0 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat)))) _v39) (fun (_v47 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12))) =>
(@_v40 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (3
  : Nat) (@instOfNatNat (3 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12) _v47))))) (∀ (_v47 :
  (@Nat)),
(∀ (_v48 : (@LE.le.{0} (@Nat) (@instLENat) _v47 _v46)),
(@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v11 _v12
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v11 _v12 _v47
  _v45))))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @SerializedPositiveBody.tag_reader

-- Complete literal proposition for SerializedPositiveBody.tag_reader; original proof reused.
theorem PartACanonical.Surface.m0428 :
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
(∀ (_v11 : (@Nat)),
(∀ (_v12 : (@Nat)),
(∀ (_v13 : (@Nat)),
(∀ (_v14 : (∀ (_v14 : (@Fin _v2)),
(@Bool))),
(∀ (_v15 : (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v9)),
(∀ (_v16 : (@LE.le.{0} (@Nat) (@instLENat) _v9 _v7)),
(∀ (_v17 : (@LT.lt.{0} (@Nat) (@instLTNat) _v2 _v3)),
(∀ (_v18 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v4)),
(∀ (_v19 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v5)),
(∀ (_v20 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v4 _v5) _v6)),
(∀ (_v21 : (@Eq.{(0 + 1)} (@Nat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))))),
(∀ (_v22 : (∀ (_v22 : (@Nat)),
(∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) _v22 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 _v22) (@_v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v22 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))))),
(∀ (_v23 : (∀ (_v23 : (@Nat)),
(∀ (_v24 : (@Nat)),
(∀ (_v25 : (@LE.le.{0} (@Nat) (@instLENat) _v23 _v24)),
(∀ (_v26 : (@LE.le.{0} (@Nat) (@instLENat) _v24 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@LE.le.{0} (@Nat) (@instLENat) (@_v0 _v23) (@_v0 _v24))))))),
(∀ (_v24 : (∀ (_v24 : (@Nat)),
(∀ (_v25 : (@LE.le.{0} (@Nat) (@instLENat) _v24 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 (@_v0 _v24)) (@Option.none.{0} (@Bool)))))),
(∀ (_v25 : (∀ (_v25 : (@Nat)),
(∀ (_v26 : (@Nat)),
(∀ (_v27 : (@LT.lt.{0} (@Nat) (@instLTNat) _v25 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))),
(∀ (_v28 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 _v25) _v26)),
(∀ (_v29 : (@LT.lt.{0} (@Nat) (@instLTNat) _v26 (@_v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v25 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))),
(@Exists.{(0 + 1)} (@Bool) (fun (_v30 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v26) (@Option.some.{0} (@Bool) _v30)))))))))),
(∀ (_v26 : (@Eq.{(0 + 1)} (@Nat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@_v0 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v7) (@OfNat.ofNat.{0} (@Nat)
  (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v27 : (@Eq.{(0 + 1)} (@Nat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@_v0 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) _v7)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))),
(∀ (_v28 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v2) (@Option.none.{0} (@Bool)))),
(∀ (_v29 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v3) (@Option.none.{0} (@Bool)))),
(∀ (_v30 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v4) (@Option.none.{0} (@Bool)))),
(∀ (_v31 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v6) (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v32 : (∀ (_v32 : (@Nat)),
(∀ (_v33 : (@LT.lt.{0} (@Nat) (@instLTNat) _v2 _v32)),
(∀ (_v34 : (@LT.lt.{0} (@Nat) (@instLTNat) _v32 _v3)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v35 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v32) (@Option.some.{0} (@Bool) _v35)))))))),
(∀ (_v33 : (∀ (_v33 : (@Nat)),
(∀ (_v34 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 _v33)),
(∀ (_v35 : (@LT.lt.{0} (@Nat) (@instLTNat) _v33 _v4)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v36 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v33) (@Option.some.{0} (@Bool) _v36)))))))),
(∀ (_v34 : (∀ (_v34 : (@Nat)),
(∀ (_v35 : (@LT.lt.{0} (@Nat) (@instLTNat) _v4 _v34)),
(∀ (_v36 : (@LE.le.{0} (@Nat) (@instLENat) _v34 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v4 _v5))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v34) (@Option.some.{0} (@Bool) (@Bool.true))))))),
(∀ (_v35 : (∀ (_v35 : (@Nat)),
(∀ (_v36 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v4 _v5) _v35)),
(∀ (_v37 : (@LT.lt.{0} (@Nat) (@instLTNat) _v35 _v6)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v35) (@Option.none.{0} (@Bool))))))),
(∀ (_v36 : (∀ (_v36 : (@Nat)),
(∀ (_v37 : (@LE.le.{0} (@Nat) (@instLENat) _v8 _v36)),
(∀ (_v38 : (@LT.lt.{0} (@Nat) (@instLTNat) _v36 _v2)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 _v36) (@Option.some.{0} (@Bool) (@_v14 (@Fin.mk _v2 _v36 _v38)))))))),
(∀ (_v37 : (@LE.le.{0} (@Nat) (@instLENat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))
  _v13)),
(∀ (_v38 : (@LT.lt.{0} (@Nat) (@instLTNat) _v13 (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12))),
(∀ (_v39 : (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12))),
(let _v40 : (∀ (_v40 : (@Nat)),
(∀ (_v41 : (@Nat)),
(@Option.{0} (@Bool)))) := (fun (_v40 : (@Nat)) =>
(fun (_v41 : (@Nat)) =>
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@Eq.{(0 + 1)} (@Nat) _v41 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v8 _v40)) (@LT.lt.{0} (@Nat) (@instLTNat) _v41 _v2)) (@instDecidableAnd (@Eq.{(0 +
  1)} (@Nat) _v41 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v8 _v40)) (@LT.lt.{0}
  (@Nat) (@instLTNat) _v41 _v2) (@instDecidableEqNat _v41 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v8 _v40)) (@Nat.decLt _v41 _v2)) (@Option.none.{0} (@Bool)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And
  (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v41) (@LT.lt.{0}
  (@Nat) (@instLTNat) _v41 (@_v0 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))) (@instDecidableAnd
  (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v41) (@LT.lt.{0}
  (@Nat) (@instLTNat) _v41 (@_v0 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))) (@Nat.decLt (@_v0
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v41) (@Nat.decLt _v41 (@_v0 (@OfNat.ofNat.{0} (@Nat) (5
  : Nat) (@instOfNatNat (5 : Nat)))))) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat) (@instLENat)
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v41 (@_v0 (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat))))) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v9
  _v40)) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v41 (@_v0
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHSub.{0} (@Nat) (@instSubNat)) _v9 _v40)))) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat)
  (@instLTNat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) _v41) (@LT.lt.{0} (@Nat)
  (@instLTNat) _v41 (@_v0 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))))) (@instDecidableAnd
  (@LT.lt.{0} (@Nat) (@instLTNat) (@_v0 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) _v41) (@LT.lt.{0}
  (@Nat) (@instLTNat) _v41 (@_v0 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat))))) (@Nat.decLt (@_v0
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) _v41) (@Nat.decLt _v41 (@_v0 (@OfNat.ofNat.{0} (@Nat)
  (12 : Nat) (@instOfNatNat (12 : Nat)))))) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat) (@instLENat)
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v41 (@_v0 (@OfNat.ofNat.{0} (@Nat) (11
  : Nat) (@instOfNatNat (11 : Nat))))) _v40) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v41 (@_v0 (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))) _v40))) (@_v1 _v41))))));
(let _v41 : (@Bool) := (@Pnp4.Frontier.ContractExpansion.padRead _v2 _v14 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v8 _v10));
(let _v42 : (@Bool) := (@Pnp4.Frontier.ContractExpansion.padRead _v2 _v14 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v8 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  _v10 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))));
(let _v43 : (@Bool) := (@Pnp4.Frontier.ContractExpansion.padRead _v2 _v14 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v8 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  _v10 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))));
(let _v44 : (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))) := (@ite.{(0 + 1)} (@Fin
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))) (@Eq.{(0 + 1)} (@Bool) _v41 (@Bool.true))
  (@instDecidableEqBool _v41 (@Bool.true)) (@ite.{(0 + 1)} (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 :
  Nat)))) (@Eq.{(0 + 1)} (@Bool) _v42 (@Bool.true)) (@instDecidableEqBool _v42 (@Bool.true)) (@OfNat.ofNat.{0} (@Fin
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))) (6 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (9 :
  Nat) (@instOfNatNat (9 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))) (6 :
  Nat))) (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))) (5 : Nat) (@Fin.instOfNat
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (8 : Nat)
  (@instOfNatNat (8 : Nat)))) (5 : Nat)))) (@ite.{(0 + 1)} (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 :
  Nat)))) (@Eq.{(0 + 1)} (@Bool) _v42 (@Bool.true)) (@instDecidableEqBool _v42 (@Bool.true)) (@OfNat.ofNat.{0} (@Fin
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))) (4 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (9 :
  Nat) (@instOfNatNat (9 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))) (4 :
  Nat))) (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))) (3 : Nat) (@Fin.instOfNat
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} (@Nat) (8 : Nat)
  (@instOfNatNat (8 : Nat)))) (3 : Nat)))));
(let _v45 : (@Pnp3.Complexity.Uniform.V1.Config (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v11
  _v12) := (@Pnp3.Complexity.Uniform.V1.Config.mk (@OfNat.ofNat.{0} (@Nat) (7500 : Nat) (@instOfNatNat (7500 : Nat))) _v11
  _v12 (@SerializedBodyRefinement.getEntry (@OfNat.ofNat.{0} (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 :
  Nat)))) (0 : Nat) (@Fin.instOfNat (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@Nat.instNeZeroSucc
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))) (0 : Nat))) (@SerializedBody.sourceMode _v2 _v14
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v8 _v10))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12) (@_v0 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  _v39) (fun (_v45 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12))) =>
(@_v40 _v10 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12) _v45))));
(@And (∀ (_v46 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@GetElem?.getElem?.{0, 0, 0} (@List.{0} (@Bool)) (@Nat) (@Bool) (fun (_v47 :
  (@List.{0} (@Bool))) =>
(fun (_v48 : (@Nat)) =>
(@LT.lt.{0} (@Nat) (@instLTNat) _v48 (@List.length.{0} (@Bool) _v47)))) (@List.instGetElem?NatLtLength.{0} (@Bool))
  (@SerializedBody.window _v2 _v14 _v8 _v9) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v10 (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v46))) (@Option.some.{0}
  (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead _v2 _v14 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v8 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v46))))))) (@Exists.{(0 + 1)} (@Nat) (fun (_v46 : (@Nat))
  =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v46 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (256 : Nat) (@instOfNatNat (256 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@And
  (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v11 _v12) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v11 _v12
  _v46 _v45) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v11 _v12 (@SerializedBodyRefinement.getExit _v44 _v43 (@SerializedBody.sourceMode _v2 _v14
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v8 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))))))
  (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12) (@_v0 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat)))) _v39) (fun (_v47 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12))) =>
(@_v40 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (3
  : Nat) (@instOfNatNat (3 : Nat)))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12) _v47))))) (∀ (_v47 :
  (@Nat)),
(∀ (_v48 : (@LE.le.{0} (@Nat) (@instLENat) _v47 _v46)),
(@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SerializedBody.machine)) _v11 _v12
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SerializedBody.machine) _v11 _v12 _v47
  _v45))))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @SerializedPositiveBody.tag_reader

-- Independent literal expected type for SmallIngress.Audit.check_preserves_nonreject.
noncomputable def PartACanonical.Types.p0703 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ (_v2 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.prefixed)) _v0 _v1)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.prefixed))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.prefixed)) _v0 _v1
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.prefixed) _v0 _v1 _v3 _v2))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.prefixed)))),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SmallIngress.producer)) _v0 _v1) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SmallIngress.producer) _v0 _v1 _v3
  (@SmallIngress.liftOld _v0 _v1 _v2)) (@SmallIngress.liftOld _v0 _v1 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.prefixed) _v0 _v1 _v3 _v2)))))))) := by
  exact @SmallIngress.Audit.check_preserves_nonreject

-- Complete literal proposition for SmallIngress.Audit.check_preserves_nonreject; original proof reused.
theorem PartACanonical.Surface.m0429 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ (_v2 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.prefixed)) _v0 _v1)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.prefixed))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.prefixed)) _v0 _v1
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.prefixed) _v0 _v1 _v3 _v2))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.prefixed)))),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SmallIngress.producer)) _v0 _v1) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SmallIngress.producer) _v0 _v1 _v3
  (@SmallIngress.liftOld _v0 _v1 _v2)) (@SmallIngress.liftOld _v0 _v1 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.prefixed) _v0 _v1 _v3 _v2)))))))) := by
  exact @SmallIngress.Audit.check_preserves_nonreject

-- Independent literal expected type for SmallIngress.Audit.check_producer_small_modes.
noncomputable def PartACanonical.Types.p0704 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(∀ (_v4 : (∀ (_v4 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v5 : (@LE.le.{0} (@Nat) (@instLENat) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) _v2)),
(∀ (_v6 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v2 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))),
(∀ (_v7 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v4 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))
  (@Option.some.{0} (@Bool) (@Bool.true)))),
(∀ (_v8 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v4 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))
  (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v9 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v4 (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))))
  (@Option.some.{0} (@Bool) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0
  : Nat))))))),
(∀ (_v10 : (∀ (_v10 : (@Ne.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v4 (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))))
  (@Option.some.{0} (@Bool) (@Bool.true))))),
(∀ (_v11 : (∀ (_v11 : (@Ne.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v4 (@OfNat.ofNat.{0} (@Nat) (10 : Nat) (@instOfNatNat (10 : Nat))))
  (@Option.some.{0} (@Bool) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2
  : Nat)))))))),
(∀ (_v12 : (∀ (_v12 : (@Nat)),
(∀ (_v13 : (@LT.lt.{0} (@Nat) (@instLTNat) _v12 _v2)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v14 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v4 _v12) (@Option.some.{0} (@Bool) _v14))))))),
(∀ (_v13 : (∀ (_v13 : (@Nat)),
(∀ (_v14 : (@LE.le.{0} (@Nat) (@instLENat) _v2 _v13)),
(∀ (_v15 : (@LE.le.{0} (@Nat) (@instLENat) _v13 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v2 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v4 _v13) (@Option.none.{0} (@Bool))))))),
(@Exists.{(0 + 1)} (@Nat) (fun (_v14 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v14 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (6 : Nat) (@instOfNatNat (6 : Nat))) _v2) (@OfNat.ofNat.{0} (@Nat) (100 : Nat) (@instOfNatNat (100 : Nat))))) (@Eq.{(0 +
  1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SmallIngress.producer)) _v0
  _v1) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SmallIngress.producer) _v0 _v1 _v14
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SmallIngress.producer)) _v0
  _v1 (@SmallIngress.q (@OfNat.ofNat.{0} (@Nat) (124 : Nat) (@instOfNatNat (124 : Nat)))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))
  (@dite.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat
  (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))) (fun (_v15 : (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))) =>
(@Decidable.byContradiction (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 :
  Nat))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat
  (8 : Nat))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (fun (_v16 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat)
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)))) =>
(@SmallIngress.producer_small_modes._proof_1 _v0 _v1 _v2 _v3 _v6 (@Eq.mp.{0} (@LE.le.{0} (@Nat) (@instLENat) (@ite.{(0 +
  1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat)
  (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 :
  Nat)))) _v2) (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) _v2)
  (@congrArg.{(0 + 1), (0 + 1)} (@Nat) (Sort 0) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 :
  Nat))) (fun (_v17 : (@Nat)) =>
(@LE.le.{0} (@Nat) (@instLENat) _v17 _v2)) (@if_pos.{(0 + 1)} (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat)
  (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v15 (@Nat) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))) _v5) _v16)))) (fun (_v15 : (@Not (@Eq.{(0 + 1)} (@Nat)
  (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))))) =>
(@Decidable.byContradiction (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 :
  Nat))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat
  (8 : Nat))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (fun (_v16 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat)
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)))) =>
(@SmallIngress.producer_small_modes._proof_2 _v0 _v1 _v2 _v6 (@Eq.mp.{0} (@LE.le.{0} (@Nat) (@instLENat) (@ite.{(0 + 1)}
  (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat)
  (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 :
  Nat)))) _v2) (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))) _v2)
  (@congrArg.{(0 + 1), (0 + 1)} (@Nat) (Sort 0) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11
  : Nat))) (fun (_v17 : (@Nat)) =>
(@LE.le.{0} (@Nat) (@instLENat) _v17 _v2)) (@if_neg.{(0 + 1)} (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat)
  (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v15 (@Nat) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))) _v5) _v16)))))) (fun (_v15 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))) =>
(@_v4 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v15))))) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SmallIngress.producer)) _v0 _v1
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@SmallIngress.producer)) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v0 _v1) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0
  : Nat)))) (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat)))) (@dite.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@ite.{(0 + 1)}
  (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat)
  (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat))))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0
  _v1)) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat)
  (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (fun (_v15 :
  (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))) =>
(@Eq.mpr.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@ite.{(0 + 1)}
  (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat)
  (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat))))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0
  _v1)) (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (@id.{0} (@Eq.{(0 + 1)} (Sort 0) (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))) (@congrArg.{(0 + 1), (0 + 1)} (@Nat)
  (Sort 0) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 :
  Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0
  : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (fun (_v16 : (@Nat)) =>
(@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v16) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))) (@if_pos.{(0 + 1)} (@Eq.{(0 + 1)}
  (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))
  _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v15 (@Nat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@Decidable.byContradiction
  (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (fun (_v16 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)))) =>
(@SmallIngress.producer_small_modes._proof_3 _v0 _v1 _v2 _v3 _v6 _v16))))) (fun (_v15 : (@Not (@Eq.{(0 + 1)} (@Nat)
  (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))))) =>
(@Eq.mpr.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@ite.{(0 + 1)}
  (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat)
  (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat))))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0
  _v1)) (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (@id.{0} (@Eq.{(0 + 1)} (Sort 0) (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v2 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))) (@congrArg.{(0 + 1), (0 + 1)} (@Nat)
  (Sort 0) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 :
  Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0
  : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (fun (_v16 : (@Nat)) =>
(@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v16) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))) (@if_neg.{(0 + 1)} (@Eq.{(0 + 1)}
  (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))
  _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v15 (@Nat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@Decidable.byContradiction
  (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (fun (_v16 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)))) =>
(@SmallIngress.producer_small_modes._proof_4 _v0 _v1 _v2 _v3 _v6 _v16))))))) (fun (_v15 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))) =>
(@SmallIngress.seeded _v4 _v2 (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v15)))))))))))))))))))))) := by
  exact @SmallIngress.Audit.check_producer_small_modes

-- Complete literal proposition for SmallIngress.Audit.check_producer_small_modes; original proof reused.
theorem PartACanonical.Surface.m0430 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(∀ (_v4 : (∀ (_v4 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v5 : (@LE.le.{0} (@Nat) (@instLENat) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) _v2)),
(∀ (_v6 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v2 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))),
(∀ (_v7 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v4 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))
  (@Option.some.{0} (@Bool) (@Bool.true)))),
(∀ (_v8 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v4 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))
  (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v9 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v4 (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))))
  (@Option.some.{0} (@Bool) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0
  : Nat))))))),
(∀ (_v10 : (∀ (_v10 : (@Ne.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v4 (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))))
  (@Option.some.{0} (@Bool) (@Bool.true))))),
(∀ (_v11 : (∀ (_v11 : (@Ne.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v4 (@OfNat.ofNat.{0} (@Nat) (10 : Nat) (@instOfNatNat (10 : Nat))))
  (@Option.some.{0} (@Bool) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2
  : Nat)))))))),
(∀ (_v12 : (∀ (_v12 : (@Nat)),
(∀ (_v13 : (@LT.lt.{0} (@Nat) (@instLTNat) _v12 _v2)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v14 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v4 _v12) (@Option.some.{0} (@Bool) _v14))))))),
(∀ (_v13 : (∀ (_v13 : (@Nat)),
(∀ (_v14 : (@LE.le.{0} (@Nat) (@instLENat) _v2 _v13)),
(∀ (_v15 : (@LE.le.{0} (@Nat) (@instLENat) _v13 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v2 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v4 _v13) (@Option.none.{0} (@Bool))))))),
(@Exists.{(0 + 1)} (@Nat) (fun (_v14 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v14 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (6 : Nat) (@instOfNatNat (6 : Nat))) _v2) (@OfNat.ofNat.{0} (@Nat) (100 : Nat) (@instOfNatNat (100 : Nat))))) (@Eq.{(0 +
  1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SmallIngress.producer)) _v0
  _v1) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SmallIngress.producer) _v0 _v1 _v14
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SmallIngress.producer)) _v0
  _v1 (@SmallIngress.q (@OfNat.ofNat.{0} (@Nat) (124 : Nat) (@instOfNatNat (124 : Nat)))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))
  (@dite.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat
  (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))) (fun (_v15 : (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))) =>
(@Decidable.byContradiction (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 :
  Nat))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat
  (8 : Nat))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (fun (_v16 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat)
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)))) =>
(@SmallIngress.producer_small_modes._proof_1 _v0 _v1 _v2 _v3 _v6 (@Eq.mp.{0} (@LE.le.{0} (@Nat) (@instLENat) (@ite.{(0 +
  1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat)
  (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 :
  Nat)))) _v2) (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) _v2)
  (@congrArg.{(0 + 1), (0 + 1)} (@Nat) (Sort 0) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 :
  Nat))) (fun (_v17 : (@Nat)) =>
(@LE.le.{0} (@Nat) (@instLENat) _v17 _v2)) (@if_pos.{(0 + 1)} (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat)
  (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v15 (@Nat) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))) _v5) _v16)))) (fun (_v15 : (@Not (@Eq.{(0 + 1)} (@Nat)
  (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))))) =>
(@Decidable.byContradiction (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 :
  Nat))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat
  (8 : Nat))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (fun (_v16 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat)
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)))) =>
(@SmallIngress.producer_small_modes._proof_2 _v0 _v1 _v2 _v6 (@Eq.mp.{0} (@LE.le.{0} (@Nat) (@instLENat) (@ite.{(0 + 1)}
  (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat)
  (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 :
  Nat)))) _v2) (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))) _v2)
  (@congrArg.{(0 + 1), (0 + 1)} (@Nat) (Sort 0) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11
  : Nat))) (fun (_v17 : (@Nat)) =>
(@LE.le.{0} (@Nat) (@instLENat) _v17 _v2)) (@if_neg.{(0 + 1)} (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat)
  (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v15 (@Nat) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))) _v5) _v16)))))) (fun (_v15 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))) =>
(@_v4 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v15))))) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SmallIngress.producer)) _v0 _v1
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@SmallIngress.producer)) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v0 _v1) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0
  : Nat)))) (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat)))) (@dite.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@ite.{(0 + 1)}
  (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat)
  (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat))))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0
  _v1)) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat)
  (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (fun (_v15 :
  (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))) =>
(@Eq.mpr.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@ite.{(0 + 1)}
  (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat)
  (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat))))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0
  _v1)) (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (@id.{0} (@Eq.{(0 + 1)} (Sort 0) (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))) (@congrArg.{(0 + 1), (0 + 1)} (@Nat)
  (Sort 0) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 :
  Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0
  : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (fun (_v16 : (@Nat)) =>
(@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v16) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))) (@if_pos.{(0 + 1)} (@Eq.{(0 + 1)}
  (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))
  _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v15 (@Nat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@Decidable.byContradiction
  (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (fun (_v16 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)))) =>
(@SmallIngress.producer_small_modes._proof_3 _v0 _v1 _v2 _v3 _v6 _v16))))) (fun (_v15 : (@Not (@Eq.{(0 + 1)} (@Nat)
  (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))))) =>
(@Eq.mpr.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@ite.{(0 + 1)}
  (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat)
  (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat))))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0
  _v1)) (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (@id.{0} (@Eq.{(0 + 1)} (Sort 0) (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v2 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))) (@congrArg.{(0 + 1), (0 + 1)} (@Nat)
  (Sort 0) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 :
  Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0
  : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (fun (_v16 : (@Nat)) =>
(@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v16) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))) (@if_neg.{(0 + 1)} (@Eq.{(0 + 1)}
  (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))
  _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v15 (@Nat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@Decidable.byContradiction
  (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (fun (_v16 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)))) =>
(@SmallIngress.producer_small_modes._proof_4 _v0 _v1 _v2 _v3 _v6 _v16))))))) (fun (_v15 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))) =>
(@SmallIngress.seeded _v4 _v2 (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v15)))))))))))))))))))))) := by
  exact @SmallIngress.Audit.check_producer_small_modes

-- Independent literal expected type for SmallIngress.Audit.check_raw_small_physical.
noncomputable def PartACanonical.Types.p0706 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ (_v2 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v0)),
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v4 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(∀ (_v5 : (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.tagMatches (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1) (@Fin.append.{(0 + 1)} _v0 _v1 (@Bool) _v2 _v3))
  (@Bool.true))),
(∀ (_v6 : (@LE.le.{0} (@Nat) (@instLENat) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v4) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v4) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1))),
(∀ (_v7 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.physicalSymbol
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1) (@Fin.append.{(0 + 1)} _v0 _v1
  (@Bool) _v2 _v3) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))) (@Option.some.{0} (@Bool) (@BEq.beq.{0}
  (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))) _v4) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))))),
(∀ (_v8 : (∀ (_v8 : (@Ne.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v4)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.physicalSymbol (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1) (@Fin.append.{(0 + 1)} _v0 _v1 (@Bool) _v2 _v3)
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))) (@Option.some.{0} (@Bool) (@Bool.true))))),
(∀ (_v9 : (∀ (_v9 : (@Ne.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v4)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.physicalSymbol (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1) (@Fin.append.{(0 + 1)} _v0 _v1 (@Bool) _v2 _v3)
  (@OfNat.ofNat.{0} (@Nat) (10 : Nat) (@instOfNatNat (10 : Nat)))) (@Option.some.{0} (@Bool) (@BEq.beq.{0} (@Nat)
  (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat))) _v4) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))))),
(let _v10 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1);
(let _v11 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation _v10);
(let _v12 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1);
(let _v13 : (∀ (_v13 : (@Nat)),
(@Option.{0} (@Bool))) := (@Body.extend (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) _v11
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencedContentTape _v0 _v1 _v11 _v2 _v3));
(let _v14 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v12 (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v4) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0
  : Nat)))) (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v4)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v15 : (@Nat)) =>
(@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) _v14 (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11)) (fun (_v16 :
  (@LT.lt.{0} (@Nat) (@instLTNat) _v14 (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11))) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v15 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))) (∀ (_v17 : (@Nat)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SmallIngress.machine)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) _v11)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SmallIngress.machine) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  _v0 _v1) _v11 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v15 _v17)
  (@Pnp3.Complexity.Uniform.V1.initialConfig (@SmallIngress.machine) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  _v0 _v1) _v11 (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v0 _v1 _v2 _v3)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@SmallIngress.producer) (@Stream.machine) _v10 _v11
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Stream.machine) _v10 _v11 _v17 (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Stream.machine)) _v10 _v11
  (@Pnp3.Complexity.Uniform.V1.UniformTM.start (@Stream.machine)) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v10
  _v11) _v14 _v16) (fun (_v18 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11))) =>
(@SmallIngress.seeded _v13 _v12 (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v4) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11) _v18)))))))))))))))))))))))))))) := by
  exact @SmallIngress.Audit.check_raw_small_physical

-- Complete literal proposition for SmallIngress.Audit.check_raw_small_physical; original proof reused.
theorem PartACanonical.Surface.m0432 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ (_v2 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v0)),
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v4 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(∀ (_v5 : (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.tagMatches (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1) (@Fin.append.{(0 + 1)} _v0 _v1 (@Bool) _v2 _v3))
  (@Bool.true))),
(∀ (_v6 : (@LE.le.{0} (@Nat) (@instLENat) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v4) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v4) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1))),
(∀ (_v7 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.physicalSymbol
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1) (@Fin.append.{(0 + 1)} _v0 _v1
  (@Bool) _v2 _v3) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))) (@Option.some.{0} (@Bool) (@BEq.beq.{0}
  (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))) _v4) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))))),
(∀ (_v8 : (∀ (_v8 : (@Ne.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v4)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.physicalSymbol (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1) (@Fin.append.{(0 + 1)} _v0 _v1 (@Bool) _v2 _v3)
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))) (@Option.some.{0} (@Bool) (@Bool.true))))),
(∀ (_v9 : (∀ (_v9 : (@Ne.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v4)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.physicalSymbol (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1) (@Fin.append.{(0 + 1)} _v0 _v1 (@Bool) _v2 _v3)
  (@OfNat.ofNat.{0} (@Nat) (10 : Nat) (@instOfNatNat (10 : Nat)))) (@Option.some.{0} (@Bool) (@BEq.beq.{0} (@Nat)
  (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat))) _v4) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))))),
(let _v10 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1);
(let _v11 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation _v10);
(let _v12 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1);
(let _v13 : (∀ (_v13 : (@Nat)),
(@Option.{0} (@Bool))) := (@Body.extend (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) _v11
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencedContentTape _v0 _v1 _v11 _v2 _v3));
(let _v14 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v12 (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v4) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0
  : Nat)))) (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v4)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v15 : (@Nat)) =>
(@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) _v14 (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11)) (fun (_v16 :
  (@LT.lt.{0} (@Nat) (@instLTNat) _v14 (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11))) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v15 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))) (∀ (_v17 : (@Nat)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SmallIngress.machine)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) _v11)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SmallIngress.machine) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  _v0 _v1) _v11 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v15 _v17)
  (@Pnp3.Complexity.Uniform.V1.initialConfig (@SmallIngress.machine) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  _v0 _v1) _v11 (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v0 _v1 _v2 _v3)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@SmallIngress.producer) (@Stream.machine) _v10 _v11
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Stream.machine) _v10 _v11 _v17 (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Stream.machine)) _v10 _v11
  (@Pnp3.Complexity.Uniform.V1.UniformTM.start (@Stream.machine)) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v10
  _v11) _v14 _v16) (fun (_v18 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11))) =>
(@SmallIngress.seeded _v13 _v12 (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v4) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11) _v18)))))))))))))))))))))))))))) := by
  exact @SmallIngress.Audit.check_raw_small_physical

-- Independent literal expected type for SmallIngress.Audit.pin_Target_AcceptedOrbit.
noncomputable def PartACanonical.Types.p0707 :
(∀ (_v0 : (@Nat)),
(Sort 0)) := by
  exact @SmallIngress.Audit.pin_Target_AcceptedOrbit

-- Independent literal expected type for SmallIngress.Audit.pin_liftOld.
noncomputable def PartACanonical.Types.p0708 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ (_v2 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.prefixed)) _v0 _v1)),
(@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SmallIngress.producer)) _v0
  _v1)))) := by
  exact @SmallIngress.Audit.pin_liftOld

-- Independent literal expected type for SmallIngress.Audit.pin_machine.
noncomputable def PartACanonical.Types.p0709 :
(@Pnp3.Complexity.Uniform.V1.UniformTM) := by
  exact @SmallIngress.Audit.pin_machine

-- Independent literal expected type for SmallIngress.Audit.pin_prepared.
noncomputable def PartACanonical.Types.p0710 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v0)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  _v2))),
(@Option.{0} (@Bool)))))))))) := by
  exact @SmallIngress.Audit.pin_prepared

-- Independent literal expected type for SmallIngress.Audit.pin_producer.
noncomputable def PartACanonical.Types.p0711 :
(@Pnp3.Complexity.Uniform.V1.UniformTM) := by
  exact @SmallIngress.Audit.pin_producer

-- Independent literal expected type for SmallIngress.Audit.pin_q.
noncomputable def PartACanonical.Types.p0712 :
(∀ (_v0 : (@Nat)),
(@Fin (@OfNat.ofNat.{0} (@Nat) (288 : Nat) (@instOfNatNat (288 : Nat))))) := by
  exact @SmallIngress.Audit.pin_q

-- Independent literal expected type for SmallIngress.Audit.pin_rows.
noncomputable def PartACanonical.Types.p0713 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (288 : Nat) (@instOfNatNat (288 : Nat))))),
(∀ (_v1 : (@Option.{0} (@Bool))),
(@Prod.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (288 : Nat) (@instOfNatNat (288 : Nat)))) (@Prod.{0, 0} (@Option.{0}
  (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))))) := by
  exact @SmallIngress.Audit.pin_rows

-- Independent literal expected type for SmallIngress.Audit.pin_seeded.
noncomputable def PartACanonical.Types.p0714 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(@Option.{0} (@Bool)))))) := by
  exact @SmallIngress.Audit.pin_seeded

-- Independent literal expected type for SmallIngress.Fixtures.canonical_nonvacuity.
noncomputable def PartACanonical.Types.p0715 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(∀ (_v2 : (@Bool)),
(let _v3 : (@Pnp4.Frontier.TreeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) :=
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0));
(let _v4 : (@Pnp4.Frontier.ContractExpansion.PrefixBitVec (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v3 (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat))) _v1))) := (@Pnp4.Frontier.ContractExpansion.zeroPrefixQueryValue
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v3 (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat))) _v1) (fun (_v4 : (@Fin (@Pnp3.Models.Partial.tableLen (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))) _v1)))) =>
_v2));
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring (@Pnp3.ComplexityInterfaces.certificateLength
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v3 (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v1)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat))))) (fun (_v5 : (@Pnp3.Complexity.Uniform.V1.Bitstring (@Pnp3.ComplexityInterfaces.certificateLength
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v3 (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v1)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))))) =>
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v3 (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v1)) (@Pnp3.ComplexityInterfaces.certificateLength
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v3 (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v1)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))) _v4 _v5) (@Bool.true))))))))) := by
  exact @SmallIngress.Fixtures.canonical_nonvacuity

-- Complete literal proposition for SmallIngress.Fixtures.canonical_nonvacuity; original proof reused.
theorem PartACanonical.Surface.m0433 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(∀ (_v2 : (@Bool)),
(let _v3 : (@Pnp4.Frontier.TreeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) :=
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0));
(let _v4 : (@Pnp4.Frontier.ContractExpansion.PrefixBitVec (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v3 (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat))) _v1))) := (@Pnp4.Frontier.ContractExpansion.zeroPrefixQueryValue
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v3 (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat))) _v1) (fun (_v4 : (@Fin (@Pnp3.Models.Partial.tableLen (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))) _v1)))) =>
_v2));
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring (@Pnp3.ComplexityInterfaces.certificateLength
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v3 (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v1)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat))))) (fun (_v5 : (@Pnp3.Complexity.Uniform.V1.Bitstring (@Pnp3.ComplexityInterfaces.certificateLength
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v3 (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v1)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))))) =>
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v3 (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v1)) (@Pnp3.ComplexityInterfaces.certificateLength
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v3 (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v1)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))) _v4 _v5) (@Bool.true))))))))) := by
  exact @SmallIngress.Fixtures.canonical_nonvacuity

-- Independent literal expected type for SmallIngress.Fixtures.check_canonical_nonvacuity.
noncomputable def PartACanonical.Types.p0716 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(∀ (_v2 : (@Bool)),
(let _v3 : (@Pnp4.Frontier.TreeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) :=
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0));
(let _v4 : (@Pnp4.Frontier.ContractExpansion.PrefixBitVec (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v3 (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat))) _v1))) := (@Pnp4.Frontier.ContractExpansion.zeroPrefixQueryValue
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v3 (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat))) _v1) (fun (_v4 : (@Fin (@Pnp3.Models.Partial.tableLen (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))) _v1)))) =>
_v2));
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring (@Pnp3.ComplexityInterfaces.certificateLength
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v3 (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v1)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat))))) (fun (_v5 : (@Pnp3.Complexity.Uniform.V1.Bitstring (@Pnp3.ComplexityInterfaces.certificateLength
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v3 (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v1)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))))) =>
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v3 (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v1)) (@Pnp3.ComplexityInterfaces.certificateLength
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v3 (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v1)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))) _v4 _v5) (@Bool.true))))))))) := by
  exact @SmallIngress.Fixtures.check_canonical_nonvacuity

-- Complete literal proposition for SmallIngress.Fixtures.check_canonical_nonvacuity; original proof reused.
theorem PartACanonical.Surface.m0434 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(∀ (_v2 : (@Bool)),
(let _v3 : (@Pnp4.Frontier.TreeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) :=
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0));
(let _v4 : (@Pnp4.Frontier.ContractExpansion.PrefixBitVec (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v3 (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat))) _v1))) := (@Pnp4.Frontier.ContractExpansion.zeroPrefixQueryValue
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v3 (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat))) _v1) (fun (_v4 : (@Fin (@Pnp3.Models.Partial.tableLen (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))) _v1)))) =>
_v2));
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring (@Pnp3.ComplexityInterfaces.certificateLength
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v3 (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v1)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat))))) (fun (_v5 : (@Pnp3.Complexity.Uniform.V1.Bitstring (@Pnp3.ComplexityInterfaces.certificateLength
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v3 (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v1)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))))) =>
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v3 (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v1)) (@Pnp3.ComplexityInterfaces.certificateLength
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v3 (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v1)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))) _v4 _v5) (@Bool.true))))))))) := by
  exact @SmallIngress.Fixtures.check_canonical_nonvacuity

-- Independent literal expected type for SmallIngress.Target.AcceptedOrbit.
noncomputable def PartACanonical.Types.p0717 :
(∀ (_v0 : (@Nat)),
(Sort 0)) := by
  exact @SmallIngress.Target.AcceptedOrbit

-- Independent literal expected type for SmallIngress.machine.
noncomputable def PartACanonical.Types.p0719 :
(@Pnp3.Complexity.Uniform.V1.UniformTM) := by
  exact @SmallIngress.machine

-- Independent literal expected type for SmallIngress.prepared.
noncomputable def PartACanonical.Types.p0720 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v0)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  _v2))),
(@Option.{0} (@Bool)))))))))) := by
  exact @SmallIngress.prepared

-- Independent literal expected type for SmallIngress.prepared.eq_1.
noncomputable def PartACanonical.Types.p0721 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v0)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  _v2))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@SmallIngress.prepared _v0 _v1 _v2 _v3 _v4 _v5 _v6 _v7) (@ite.{(0 + 1)}
  (@Option.{0} (@Bool)) (@And (@Eq.{(0 + 1)} (@Nat) _v6 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) _v2) _v7) (@OfNat.ofNat.{0} (@Nat) (7 : Nat)
  (@instOfNatNat (7 : Nat))))) (@instDecidableAnd (@Eq.{(0 + 1)} (@Nat) _v6 (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) _v2) _v7) (@OfNat.ofNat.{0} (@Nat) (7 : Nat)
  (@instOfNatNat (7 : Nat)))) (@instDecidableEqNat _v6 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@instDecidableEqNat (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) _v2) _v7) (@OfNat.ofNat.{0} (@Nat) (7 : Nat)
  (@instOfNatNat (7 : Nat))))) (@Option.none.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.countdownTape
  _v0 _v1 _v2 _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v6 _v7))))))))))) := by
  exact @SmallIngress.prepared.eq_1

-- Complete literal proposition for SmallIngress.prepared.eq_1; original proof reused.
theorem PartACanonical.Surface.m0435 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v0)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  _v2))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@SmallIngress.prepared _v0 _v1 _v2 _v3 _v4 _v5 _v6 _v7) (@ite.{(0 + 1)}
  (@Option.{0} (@Bool)) (@And (@Eq.{(0 + 1)} (@Nat) _v6 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) _v2) _v7) (@OfNat.ofNat.{0} (@Nat) (7 : Nat)
  (@instOfNatNat (7 : Nat))))) (@instDecidableAnd (@Eq.{(0 + 1)} (@Nat) _v6 (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) _v2) _v7) (@OfNat.ofNat.{0} (@Nat) (7 : Nat)
  (@instOfNatNat (7 : Nat)))) (@instDecidableEqNat _v6 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@instDecidableEqNat (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) _v2) _v7) (@OfNat.ofNat.{0} (@Nat) (7 : Nat)
  (@instOfNatNat (7 : Nat))))) (@Option.none.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.countdownTape
  _v0 _v1 _v2 _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v6 _v7))))))))))) := by
  exact @SmallIngress.prepared.eq_1

-- Independent literal expected type for SmallIngress.producer.
noncomputable def PartACanonical.Types.p0723 :
(@Pnp3.Complexity.Uniform.V1.UniformTM) := by
  exact @SmallIngress.producer

-- Independent literal expected type for SmallIngress.producer_small_modes.
noncomputable def PartACanonical.Types.p0724 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(∀ (_v4 : (∀ (_v4 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v5 : (@LE.le.{0} (@Nat) (@instLENat) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) _v2)),
(∀ (_v6 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v2 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))),
(∀ (_v7 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v4 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))
  (@Option.some.{0} (@Bool) (@Bool.true)))),
(∀ (_v8 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v4 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))
  (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v9 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v4 (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))))
  (@Option.some.{0} (@Bool) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0
  : Nat))))))),
(∀ (_v10 : (∀ (_v10 : (@Ne.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v4 (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))))
  (@Option.some.{0} (@Bool) (@Bool.true))))),
(∀ (_v11 : (∀ (_v11 : (@Ne.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v4 (@OfNat.ofNat.{0} (@Nat) (10 : Nat) (@instOfNatNat (10 : Nat))))
  (@Option.some.{0} (@Bool) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2
  : Nat)))))))),
(∀ (_v12 : (∀ (_v12 : (@Nat)),
(∀ (_v13 : (@LT.lt.{0} (@Nat) (@instLTNat) _v12 _v2)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v14 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v4 _v12) (@Option.some.{0} (@Bool) _v14))))))),
(∀ (_v13 : (∀ (_v13 : (@Nat)),
(∀ (_v14 : (@LE.le.{0} (@Nat) (@instLENat) _v2 _v13)),
(∀ (_v15 : (@LE.le.{0} (@Nat) (@instLENat) _v13 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v2 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v4 _v13) (@Option.none.{0} (@Bool))))))),
(@Exists.{(0 + 1)} (@Nat) (fun (_v14 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v14 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (6 : Nat) (@instOfNatNat (6 : Nat))) _v2) (@OfNat.ofNat.{0} (@Nat) (100 : Nat) (@instOfNatNat (100 : Nat))))) (@Eq.{(0 +
  1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SmallIngress.producer)) _v0
  _v1) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SmallIngress.producer) _v0 _v1 _v14
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SmallIngress.producer)) _v0
  _v1 (@SmallIngress.q (@OfNat.ofNat.{0} (@Nat) (124 : Nat) (@instOfNatNat (124 : Nat)))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))
  (@dite.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat
  (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))) (fun (_v15 : (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))) =>
(@Decidable.byContradiction (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 :
  Nat))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat
  (8 : Nat))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (fun (_v16 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat)
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)))) =>
(@SmallIngress.producer_small_modes._proof_1 _v0 _v1 _v2 _v3 _v6 (@Eq.mp.{0} (@LE.le.{0} (@Nat) (@instLENat) (@ite.{(0 +
  1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat)
  (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 :
  Nat)))) _v2) (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) _v2)
  (@congrArg.{(0 + 1), (0 + 1)} (@Nat) (Sort 0) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 :
  Nat))) (fun (_v17 : (@Nat)) =>
(@LE.le.{0} (@Nat) (@instLENat) _v17 _v2)) (@if_pos.{(0 + 1)} (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat)
  (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v15 (@Nat) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))) _v5) _v16)))) (fun (_v15 : (@Not (@Eq.{(0 + 1)} (@Nat)
  (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))))) =>
(@Decidable.byContradiction (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 :
  Nat))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat
  (8 : Nat))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (fun (_v16 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat)
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)))) =>
(@SmallIngress.producer_small_modes._proof_2 _v0 _v1 _v2 _v6 (@Eq.mp.{0} (@LE.le.{0} (@Nat) (@instLENat) (@ite.{(0 + 1)}
  (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat)
  (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 :
  Nat)))) _v2) (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))) _v2)
  (@congrArg.{(0 + 1), (0 + 1)} (@Nat) (Sort 0) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11
  : Nat))) (fun (_v17 : (@Nat)) =>
(@LE.le.{0} (@Nat) (@instLENat) _v17 _v2)) (@if_neg.{(0 + 1)} (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat)
  (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v15 (@Nat) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))) _v5) _v16)))))) (fun (_v15 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))) =>
(@_v4 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v15))))) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SmallIngress.producer)) _v0 _v1
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@SmallIngress.producer)) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v0 _v1) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0
  : Nat)))) (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat)))) (@dite.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@ite.{(0 + 1)}
  (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat)
  (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat))))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0
  _v1)) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat)
  (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (fun (_v15 :
  (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))) =>
(@Eq.mpr.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@ite.{(0 + 1)}
  (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat)
  (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat))))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0
  _v1)) (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (@id.{0} (@Eq.{(0 + 1)} (Sort 0) (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))) (@congrArg.{(0 + 1), (0 + 1)} (@Nat)
  (Sort 0) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 :
  Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0
  : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (fun (_v16 : (@Nat)) =>
(@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v16) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))) (@if_pos.{(0 + 1)} (@Eq.{(0 + 1)}
  (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))
  _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v15 (@Nat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@Decidable.byContradiction
  (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (fun (_v16 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)))) =>
(@SmallIngress.producer_small_modes._proof_3 _v0 _v1 _v2 _v3 _v6 _v16))))) (fun (_v15 : (@Not (@Eq.{(0 + 1)} (@Nat)
  (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))))) =>
(@Eq.mpr.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@ite.{(0 + 1)}
  (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat)
  (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat))))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0
  _v1)) (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (@id.{0} (@Eq.{(0 + 1)} (Sort 0) (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v2 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))) (@congrArg.{(0 + 1), (0 + 1)} (@Nat)
  (Sort 0) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 :
  Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0
  : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (fun (_v16 : (@Nat)) =>
(@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v16) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))) (@if_neg.{(0 + 1)} (@Eq.{(0 + 1)}
  (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))
  _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v15 (@Nat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@Decidable.byContradiction
  (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (fun (_v16 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)))) =>
(@SmallIngress.producer_small_modes._proof_4 _v0 _v1 _v2 _v3 _v6 _v16))))))) (fun (_v15 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))) =>
(@SmallIngress.seeded _v4 _v2 (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v15)))))))))))))))))))))) := by
  exact @SmallIngress.producer_small_modes

-- Complete literal proposition for SmallIngress.producer_small_modes; original proof reused.
theorem PartACanonical.Surface.m0437 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(∀ (_v4 : (∀ (_v4 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v5 : (@LE.le.{0} (@Nat) (@instLENat) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) _v2)),
(∀ (_v6 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v2 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))),
(∀ (_v7 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v4 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))
  (@Option.some.{0} (@Bool) (@Bool.true)))),
(∀ (_v8 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v4 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))
  (@Option.some.{0} (@Bool) (@Bool.false)))),
(∀ (_v9 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v4 (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))))
  (@Option.some.{0} (@Bool) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0
  : Nat))))))),
(∀ (_v10 : (∀ (_v10 : (@Ne.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v4 (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))))
  (@Option.some.{0} (@Bool) (@Bool.true))))),
(∀ (_v11 : (∀ (_v11 : (@Ne.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v4 (@OfNat.ofNat.{0} (@Nat) (10 : Nat) (@instOfNatNat (10 : Nat))))
  (@Option.some.{0} (@Bool) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2
  : Nat)))))))),
(∀ (_v12 : (∀ (_v12 : (@Nat)),
(∀ (_v13 : (@LT.lt.{0} (@Nat) (@instLTNat) _v12 _v2)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v14 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v4 _v12) (@Option.some.{0} (@Bool) _v14))))))),
(∀ (_v13 : (∀ (_v13 : (@Nat)),
(∀ (_v14 : (@LE.le.{0} (@Nat) (@instLENat) _v2 _v13)),
(∀ (_v15 : (@LE.le.{0} (@Nat) (@instLENat) _v13 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v2 (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v4 _v13) (@Option.none.{0} (@Bool))))))),
(@Exists.{(0 + 1)} (@Nat) (fun (_v14 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v14 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (6 : Nat) (@instOfNatNat (6 : Nat))) _v2) (@OfNat.ofNat.{0} (@Nat) (100 : Nat) (@instOfNatNat (100 : Nat))))) (@Eq.{(0 +
  1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SmallIngress.producer)) _v0
  _v1) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SmallIngress.producer) _v0 _v1 _v14
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SmallIngress.producer)) _v0
  _v1 (@SmallIngress.q (@OfNat.ofNat.{0} (@Nat) (124 : Nat) (@instOfNatNat (124 : Nat)))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))
  (@dite.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat
  (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))) (fun (_v15 : (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))) =>
(@Decidable.byContradiction (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 :
  Nat))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat
  (8 : Nat))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (fun (_v16 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat)
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)))) =>
(@SmallIngress.producer_small_modes._proof_1 _v0 _v1 _v2 _v3 _v6 (@Eq.mp.{0} (@LE.le.{0} (@Nat) (@instLENat) (@ite.{(0 +
  1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat)
  (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 :
  Nat)))) _v2) (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) _v2)
  (@congrArg.{(0 + 1), (0 + 1)} (@Nat) (Sort 0) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 :
  Nat))) (fun (_v17 : (@Nat)) =>
(@LE.le.{0} (@Nat) (@instLENat) _v17 _v2)) (@if_pos.{(0 + 1)} (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat)
  (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v15 (@Nat) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))) _v5) _v16)))) (fun (_v15 : (@Not (@Eq.{(0 + 1)} (@Nat)
  (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))))) =>
(@Decidable.byContradiction (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 :
  Nat))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat
  (8 : Nat))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (fun (_v16 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat)
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)))) =>
(@SmallIngress.producer_small_modes._proof_2 _v0 _v1 _v2 _v6 (@Eq.mp.{0} (@LE.le.{0} (@Nat) (@instLENat) (@ite.{(0 + 1)}
  (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat)
  (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 :
  Nat)))) _v2) (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))) _v2)
  (@congrArg.{(0 + 1), (0 + 1)} (@Nat) (Sort 0) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11
  : Nat))) (fun (_v17 : (@Nat)) =>
(@LE.le.{0} (@Nat) (@instLENat) _v17 _v2)) (@if_neg.{(0 + 1)} (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat)
  (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v15 (@Nat) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat))))) _v5) _v16)))))) (fun (_v15 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))) =>
(@_v4 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v15))))) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SmallIngress.producer)) _v0 _v1
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@SmallIngress.producer)) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v0 _v1) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0
  : Nat)))) (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat)))) (@dite.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@ite.{(0 + 1)}
  (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat)
  (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat))))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0
  _v1)) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat)
  (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (fun (_v15 :
  (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))) =>
(@Eq.mpr.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@ite.{(0 + 1)}
  (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat)
  (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat))))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0
  _v1)) (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (@id.{0} (@Eq.{(0 + 1)} (Sort 0) (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))) (@congrArg.{(0 + 1), (0 + 1)} (@Nat)
  (Sort 0) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 :
  Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0
  : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (fun (_v16 : (@Nat)) =>
(@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v16) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))) (@if_pos.{(0 + 1)} (@Eq.{(0 + 1)}
  (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))
  _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v15 (@Nat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@Decidable.byContradiction
  (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (fun (_v16 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)))) =>
(@SmallIngress.producer_small_modes._proof_3 _v0 _v1 _v2 _v3 _v6 _v16))))) (fun (_v15 : (@Not (@Eq.{(0 + 1)} (@Nat)
  (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))))) =>
(@Eq.mpr.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@ite.{(0 + 1)}
  (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat)
  (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat))))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0
  _v1)) (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (@id.{0} (@Eq.{(0 + 1)} (Sort 0) (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v2 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))) (@congrArg.{(0 + 1), (0 + 1)} (@Nat)
  (Sort 0) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 :
  Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0
  : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (fun (_v16 : (@Nat)) =>
(@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v16) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))) (@if_neg.{(0 + 1)} (@Eq.{(0 + 1)}
  (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))
  _v3) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v15 (@Nat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@Decidable.byContradiction
  (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (fun (_v16 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)))) =>
(@SmallIngress.producer_small_modes._proof_4 _v0 _v1 _v2 _v3 _v6 _v16))))))) (fun (_v15 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))) =>
(@SmallIngress.seeded _v4 _v2 (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v3) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v15)))))))))))))))))))))) := by
  exact @SmallIngress.producer_small_modes

-- Independent literal expected type for SmallIngress.q.
noncomputable def PartACanonical.Types.p0725 :
(∀ (_v0 : (@Nat)),
(@Fin (@OfNat.ofNat.{0} (@Nat) (288 : Nat) (@instOfNatNat (288 : Nat))))) := by
  exact @SmallIngress.q

-- Independent literal expected type for SmallIngress.raw_small_physical.
noncomputable def PartACanonical.Types.p0727 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ (_v2 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v0)),
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v4 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(∀ (_v5 : (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.tagMatches (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1) (@Fin.append.{(0 + 1)} _v0 _v1 (@Bool) _v2 _v3))
  (@Bool.true))),
(∀ (_v6 : (@LE.le.{0} (@Nat) (@instLENat) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v4) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v4) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1))),
(∀ (_v7 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.physicalSymbol
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1) (@Fin.append.{(0 + 1)} _v0 _v1
  (@Bool) _v2 _v3) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))) (@Option.some.{0} (@Bool) (@BEq.beq.{0}
  (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))) _v4) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))))),
(∀ (_v8 : (∀ (_v8 : (@Ne.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v4)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.physicalSymbol (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1) (@Fin.append.{(0 + 1)} _v0 _v1 (@Bool) _v2 _v3)
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))) (@Option.some.{0} (@Bool) (@Bool.true))))),
(∀ (_v9 : (∀ (_v9 : (@Ne.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v4)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.physicalSymbol (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1) (@Fin.append.{(0 + 1)} _v0 _v1 (@Bool) _v2 _v3)
  (@OfNat.ofNat.{0} (@Nat) (10 : Nat) (@instOfNatNat (10 : Nat)))) (@Option.some.{0} (@Bool) (@BEq.beq.{0} (@Nat)
  (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat))) _v4) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))))),
(let _v10 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1);
(let _v11 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation _v10);
(let _v12 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1);
(let _v13 : (∀ (_v13 : (@Nat)),
(@Option.{0} (@Bool))) := (@Body.extend (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) _v11
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencedContentTape _v0 _v1 _v11 _v2 _v3));
(let _v14 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v12 (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v4) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0
  : Nat)))) (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v4)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v15 : (@Nat)) =>
(@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) _v14 (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11)) (fun (_v16 :
  (@LT.lt.{0} (@Nat) (@instLTNat) _v14 (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11))) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v15 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))) (∀ (_v17 : (@Nat)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SmallIngress.machine)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) _v11)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SmallIngress.machine) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  _v0 _v1) _v11 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v15 _v17)
  (@Pnp3.Complexity.Uniform.V1.initialConfig (@SmallIngress.machine) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  _v0 _v1) _v11 (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v0 _v1 _v2 _v3)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@SmallIngress.producer) (@Stream.machine) _v10 _v11
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Stream.machine) _v10 _v11 _v17 (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Stream.machine)) _v10 _v11
  (@Pnp3.Complexity.Uniform.V1.UniformTM.start (@Stream.machine)) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v10
  _v11) _v14 _v16) (fun (_v18 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11))) =>
(@SmallIngress.seeded _v13 _v12 (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v4) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11) _v18)))))))))))))))))))))))))))) := by
  exact @SmallIngress.raw_small_physical

-- Complete literal proposition for SmallIngress.raw_small_physical; original proof reused.
theorem PartACanonical.Surface.m0439 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ (_v2 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v0)),
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v4 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(∀ (_v5 : (@Eq.{(0 + 1)} (@Bool) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.tagMatches (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1) (@Fin.append.{(0 + 1)} _v0 _v1 (@Bool) _v2 _v3))
  (@Bool.true))),
(∀ (_v6 : (@LE.le.{0} (@Nat) (@instLENat) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v4) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v4) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1))),
(∀ (_v7 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.physicalSymbol
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1) (@Fin.append.{(0 + 1)} _v0 _v1
  (@Bool) _v2 _v3) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))) (@Option.some.{0} (@Bool) (@BEq.beq.{0}
  (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))) _v4) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))))),
(∀ (_v8 : (∀ (_v8 : (@Ne.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v4)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.physicalSymbol (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1) (@Fin.append.{(0 + 1)} _v0 _v1 (@Bool) _v2 _v3)
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))) (@Option.some.{0} (@Bool) (@Bool.true))))),
(∀ (_v9 : (∀ (_v9 : (@Ne.{(0 + 1)} (@Nat) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v4)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.physicalSymbol (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1) (@Fin.append.{(0 + 1)} _v0 _v1 (@Bool) _v2 _v3)
  (@OfNat.ofNat.{0} (@Nat) (10 : Nat) (@instOfNatNat (10 : Nat)))) (@Option.some.{0} (@Bool) (@BEq.beq.{0} (@Nat)
  (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat))) _v4) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))))),
(let _v10 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1);
(let _v11 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation _v10);
(let _v12 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 _v1);
(let _v13 : (∀ (_v13 : (@Nat)),
(@Option.{0} (@Bool))) := (@Body.extend (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) _v11
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencedContentTape _v0 _v1 _v11 _v2 _v3));
(let _v14 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v12 (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v4) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0
  : Nat)))) (@instDecidableEqNat (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v4)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v15 : (@Nat)) =>
(@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) _v14 (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11)) (fun (_v16 :
  (@LT.lt.{0} (@Nat) (@instLTNat) _v14 (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11))) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v15 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (64 : Nat) (@instOfNatNat (64 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))) (∀ (_v17 : (@Nat)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SmallIngress.machine)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) _v11)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SmallIngress.machine) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  _v0 _v1) _v11 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v15 _v17)
  (@Pnp3.Complexity.Uniform.V1.initialConfig (@SmallIngress.machine) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  _v0 _v1) _v11 (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v0 _v1 _v2 _v3)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@SmallIngress.producer) (@Stream.machine) _v10 _v11
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@Stream.machine) _v10 _v11 _v17 (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Stream.machine)) _v10 _v11
  (@Pnp3.Complexity.Uniform.V1.UniformTM.start (@Stream.machine)) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v10
  _v11) _v14 _v16) (fun (_v18 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11))) =>
(@SmallIngress.seeded _v13 _v12 (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v4) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11) _v18)))))))))))))))))))))))))))) := by
  exact @SmallIngress.raw_small_physical

-- Independent literal expected type for SmallIngress.rows.
noncomputable def PartACanonical.Types.p0728 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (288 : Nat) (@instOfNatNat (288 : Nat))))),
(∀ (_v1 : (@Option.{0} (@Bool))),
(@Prod.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (288 : Nat) (@instOfNatNat (288 : Nat)))) (@Prod.{0, 0} (@Option.{0}
  (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))))) := by
  exact @SmallIngress.rows

-- Independent literal expected type for SmallIngress.seeded.
noncomputable def PartACanonical.Types.p0729 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(@Option.{0} (@Bool)))))) := by
  exact @SmallIngress.seeded

-- Independent literal expected type for SmallIngress.seeded.eq_1.
noncomputable def PartACanonical.Types.p0730 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@SmallIngress.seeded _v0 _v1 _v2 _v3) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And
  (@Eq.{(0 + 1)} (@Nat) _v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Eq.{(0 + 1)} (@Nat) _v3
  (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))) (@instDecidableAnd (@Eq.{(0 + 1)} (@Nat) _v2
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Eq.{(0 + 1)} (@Nat) _v3 (@OfNat.ofNat.{0} (@Nat) (7 :
  Nat) (@instOfNatNat (7 : Nat)))) (@instDecidableEqNat _v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@instDecidableEqNat _v3 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))) (@Option.none.{0} (@Bool))
  (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@Ne.{(0 + 1)} (@Nat) _v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat)))) (@Eq.{(0 + 1)} (@Nat) _v3 (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))))
  (@instDecidableAnd (@Ne.{(0 + 1)} (@Nat) _v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Eq.{(0 +
  1)} (@Nat) _v3 (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))) (@instDecidableNot (@Eq.{(0 + 1)} (@Nat)
  _v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat _v2 (@OfNat.ofNat.{0} (@Nat) (0
  : Nat) (@instOfNatNat (0 : Nat))))) (@instDecidableEqNat _v3 (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 :
  Nat))))) (@Option.none.{0} (@Bool)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@Ne.{(0 + 1)} (@Nat) _v2
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Eq.{(0 + 1)} (@Nat) _v3 (@OfNat.ofNat.{0} (@Nat) (10 :
  Nat) (@instOfNatNat (10 : Nat))))) (@instDecidableAnd (@Ne.{(0 + 1)} (@Nat) _v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))) (@Eq.{(0 + 1)} (@Nat) _v3 (@OfNat.ofNat.{0} (@Nat) (10 : Nat) (@instOfNatNat (10 : Nat))))
  (@instDecidableNot (@Eq.{(0 + 1)} (@Nat) _v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@instDecidableEqNat _v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))) (@instDecidableEqNat _v3
  (@OfNat.ofNat.{0} (@Nat) (10 : Nat) (@instOfNatNat (10 : Nat))))) (@Option.some.{0} (@Bool) (@Bool.true)) (@ite.{(0 +
  1)} (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v1 _v3) (@LT.lt.{0} (@Nat) (@instLTNat) _v3
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) _v2 (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat _v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))) (@instDecidableAnd
  (@LT.lt.{0} (@Nat) (@instLTNat) _v1 _v3) (@LT.lt.{0} (@Nat) (@instLTNat) _v3 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) _v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@instDecidableEqNat _v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 :
  Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))))) (@Nat.decLt _v1 _v3) (@Nat.decLt _v3 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) _v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@instDecidableEqNat _v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 :
  Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat)))))) (@Option.some.{0} (@Bool) (@Bool.false)) (@ite.{(0 + 1)} (@Option.{0} (@Bool))
  (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 +
  1)} (@Nat) _v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat _v2 (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat)))) _v3) (@LT.lt.{0} (@Nat) (@instLTNat) _v3 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) _v2
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat _v2 (@OfNat.ofNat.{0} (@Nat) (0 :
  Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat)
  (1 : Nat) (@instOfNatNat (1 : Nat))))) _v2) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))))
  (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@ite.{(0 + 1)}
  (@Nat) (@Eq.{(0 + 1)} (@Nat) _v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat _v2
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat)))) _v3) (@LT.lt.{0} (@Nat) (@instLTNat) _v3 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) _v2
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat _v2 (@OfNat.ofNat.{0} (@Nat) (0 :
  Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat)
  (1 : Nat) (@instOfNatNat (1 : Nat))))) _v2) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))) (@Nat.decLt
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) _v2 (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat _v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v3) (@Nat.decLt _v3
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) _v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0
  : Nat)))) (@instDecidableEqNat _v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) _v2)
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))))) (@Option.some.{0} (@Bool) (@Bool.true)) (@_v0
  _v3))))))))))) := by
  exact @SmallIngress.seeded.eq_1

-- Complete literal proposition for SmallIngress.seeded.eq_1; original proof reused.
theorem PartACanonical.Surface.m0440 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@SmallIngress.seeded _v0 _v1 _v2 _v3) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And
  (@Eq.{(0 + 1)} (@Nat) _v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Eq.{(0 + 1)} (@Nat) _v3
  (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))) (@instDecidableAnd (@Eq.{(0 + 1)} (@Nat) _v2
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Eq.{(0 + 1)} (@Nat) _v3 (@OfNat.ofNat.{0} (@Nat) (7 :
  Nat) (@instOfNatNat (7 : Nat)))) (@instDecidableEqNat _v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@instDecidableEqNat _v3 (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))) (@Option.none.{0} (@Bool))
  (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@Ne.{(0 + 1)} (@Nat) _v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat)))) (@Eq.{(0 + 1)} (@Nat) _v3 (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))))
  (@instDecidableAnd (@Ne.{(0 + 1)} (@Nat) _v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Eq.{(0 +
  1)} (@Nat) _v3 (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))) (@instDecidableNot (@Eq.{(0 + 1)} (@Nat)
  _v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat _v2 (@OfNat.ofNat.{0} (@Nat) (0
  : Nat) (@instOfNatNat (0 : Nat))))) (@instDecidableEqNat _v3 (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 :
  Nat))))) (@Option.none.{0} (@Bool)) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@Ne.{(0 + 1)} (@Nat) _v2
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Eq.{(0 + 1)} (@Nat) _v3 (@OfNat.ofNat.{0} (@Nat) (10 :
  Nat) (@instOfNatNat (10 : Nat))))) (@instDecidableAnd (@Ne.{(0 + 1)} (@Nat) _v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))) (@Eq.{(0 + 1)} (@Nat) _v3 (@OfNat.ofNat.{0} (@Nat) (10 : Nat) (@instOfNatNat (10 : Nat))))
  (@instDecidableNot (@Eq.{(0 + 1)} (@Nat) _v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@instDecidableEqNat _v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))) (@instDecidableEqNat _v3
  (@OfNat.ofNat.{0} (@Nat) (10 : Nat) (@instOfNatNat (10 : Nat))))) (@Option.some.{0} (@Bool) (@Bool.true)) (@ite.{(0 +
  1)} (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v1 _v3) (@LT.lt.{0} (@Nat) (@instLTNat) _v3
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) _v2 (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat _v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))) (@instDecidableAnd
  (@LT.lt.{0} (@Nat) (@instLTNat) _v1 _v3) (@LT.lt.{0} (@Nat) (@instLTNat) _v3 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) _v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@instDecidableEqNat _v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 :
  Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))))) (@Nat.decLt _v1 _v3) (@Nat.decLt _v3 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) _v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@instDecidableEqNat _v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 :
  Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat)))))) (@Option.some.{0} (@Bool) (@Bool.false)) (@ite.{(0 + 1)} (@Option.{0} (@Bool))
  (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 +
  1)} (@Nat) _v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat _v2 (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat)))) _v3) (@LT.lt.{0} (@Nat) (@instLTNat) _v3 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) _v2
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat _v2 (@OfNat.ofNat.{0} (@Nat) (0 :
  Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat)
  (1 : Nat) (@instOfNatNat (1 : Nat))))) _v2) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))))
  (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@ite.{(0 + 1)}
  (@Nat) (@Eq.{(0 + 1)} (@Nat) _v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat _v2
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat)))) _v3) (@LT.lt.{0} (@Nat) (@instLTNat) _v3 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) _v2
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat _v2 (@OfNat.ofNat.{0} (@Nat) (0 :
  Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat)
  (1 : Nat) (@instOfNatNat (1 : Nat))))) _v2) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))) (@Nat.decLt
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) _v2 (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat _v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) _v3) (@Nat.decLt _v3
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) _v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0
  : Nat)))) (@instDecidableEqNat _v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) _v2)
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))))) (@Option.some.{0} (@Bool) (@Bool.true)) (@_v0
  _v3))))))))))) := by
  exact @SmallIngress.seeded.eq_1

-- Independent literal expected type for SmallOrbit.Audit.check_accepted_raw.
noncomputable def PartACanonical.Types.p0731 :
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
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)) (@Exists.{(0 + 1)} (@Nat) (fun (_v7 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v8 : (@Nat)) =>
(@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v2) _v7) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
  (@Pnp4.Frontier.treeMCSPSearchProblem (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))))
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))
  (@Sigma.fst.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v9))) _v6))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)))) (fun (_v9 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v2) _v7) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
  (@Pnp4.Frontier.treeMCSPSearchProblem (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))))
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))
  (@Sigma.fst.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v9))) _v6))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros?
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2
  (@Bool) _v3 _v4)) (@Option.some.{0} (@Nat) _v7)) (@And (@LE.le.{0} (@Nat) (@instLENat) _v8 (@HMul.hMul.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4096 : Nat) (@instOfNatNat (4096 : Nat)))
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))) (let _v10 : (∀ (_v10 : (@Nat)),
(@Option.{0} (@Bool))) := (@Body.extend (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Body.installedTape (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@SmallIngress.prepared _v1 _v2 (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)) _v3 _v4 _v7
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v10))) _v6))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v7) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat)))) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v10))) _v6))));
(@And (∀ (_v11 : (@Nat)),
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) _v11 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat)
  (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v12))) _v6))))),
(@Exists.{(0 + 1)} (@Nat) (fun (_v13 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v13 _v8) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SmallIngress.machine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SmallIngress.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v13 (@Pnp3.Complexity.Uniform.V1.initialConfig (@SmallIngress.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@SmallIngress.producer) (@Stream.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Stream.machine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Stream.paid (@Stream.Target.mode _v10 (@Stream.Target.cursor (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v7)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v11) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2))) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v7)
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
  (3 : Nat)))) _v9) (fun (_v14 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@Stream.Target.image _v10 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v7
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v15))) _v6)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v7)) _v11 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 (@OfNat.ofNat.{0} (@Nat)
  (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Bool.true) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) _v14))))))))))) (@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@Stream.Target.cursor (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v7)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  _v2) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v11))) _v6)))) (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)))) (fun (_v11 : (@LT.lt.{0} (@Nat) (@instLTNat) (@Stream.Target.cursor (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v7)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v11))) _v6)))) (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SmallIngress.machine)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SmallIngress.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v8 (@Pnp3.Complexity.Uniform.V1.initialConfig (@SmallIngress.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@SmallIngress.producer) (@Stream.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Stream.machine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Stream.q (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Stream.Target.cursor (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v7)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v12))) _v6)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)) (@instDecidableEqNat (@Stream.Target.cursor (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v7)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v12))) _v6)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)) (@OfNat.ofNat.{0} (@Nat) (57 : Nat) (@instOfNatNat (57 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (58 : Nat) (@instOfNatNat (58 : Nat))))) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@Stream.Target.cursor (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v7)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0}
  (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v12))) _v6)))) _v11) (fun (_v12 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@Stream.Target.image _v10 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v7
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v13))) _v6)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v7)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v13))) _v6))) (@Bool.false) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) _v12)))))))))))))))))))))))))))) := by
  exact @SmallOrbit.Audit.check_accepted_raw

-- Complete literal proposition for SmallOrbit.Audit.check_accepted_raw; original proof reused.
theorem PartACanonical.Surface.m0441 :
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
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)) (@Exists.{(0 + 1)} (@Nat) (fun (_v7 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v8 : (@Nat)) =>
(@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v2) _v7) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
  (@Pnp4.Frontier.treeMCSPSearchProblem (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))))
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))
  (@Sigma.fst.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v9))) _v6))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)))) (fun (_v9 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v2) _v7) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
  (@Pnp4.Frontier.treeMCSPSearchProblem (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))))
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))
  (@Sigma.fst.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v9))) _v6))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros?
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2
  (@Bool) _v3 _v4)) (@Option.some.{0} (@Nat) _v7)) (@And (@LE.le.{0} (@Nat) (@instLENat) _v8 (@HMul.hMul.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4096 : Nat) (@instOfNatNat (4096 : Nat)))
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))) (let _v10 : (∀ (_v10 : (@Nat)),
(@Option.{0} (@Bool))) := (@Body.extend (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Body.installedTape (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@SmallIngress.prepared _v1 _v2 (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)) _v3 _v4 _v7
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v10))) _v6))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v7) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat)))) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v10))) _v6))));
(@And (∀ (_v11 : (@Nat)),
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) _v11 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat)
  (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v12))) _v6))))),
(@Exists.{(0 + 1)} (@Nat) (fun (_v13 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v13 _v8) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SmallIngress.machine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SmallIngress.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v13 (@Pnp3.Complexity.Uniform.V1.initialConfig (@SmallIngress.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@SmallIngress.producer) (@Stream.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Stream.machine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Stream.paid (@Stream.Target.mode _v10 (@Stream.Target.cursor (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v7)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v11) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2))) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v7)
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
  (3 : Nat)))) _v9) (fun (_v14 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@Stream.Target.image _v10 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v7
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v15))) _v6)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v7)) _v11 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 (@OfNat.ofNat.{0} (@Nat)
  (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Bool.true) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) _v14))))))))))) (@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@Stream.Target.cursor (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v7)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  _v2) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v11))) _v6)))) (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)))) (fun (_v11 : (@LT.lt.{0} (@Nat) (@instLTNat) (@Stream.Target.cursor (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v7)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v11))) _v6)))) (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SmallIngress.machine)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SmallIngress.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v8 (@Pnp3.Complexity.Uniform.V1.initialConfig (@SmallIngress.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@SmallIngress.producer) (@Stream.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Stream.machine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Stream.q (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Stream.Target.cursor (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v7)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v12))) _v6)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)) (@instDecidableEqNat (@Stream.Target.cursor (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v7)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v12))) _v6)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)) (@OfNat.ofNat.{0} (@Nat) (57 : Nat) (@instOfNatNat (57 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (58 : Nat) (@instOfNatNat (58 : Nat))))) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@Stream.Target.cursor (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v7)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0}
  (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v12))) _v6)))) _v11) (fun (_v12 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@Stream.Target.image _v10 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v7
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v13))) _v6)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v7)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v13))) _v6))) (@Bool.false) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) _v12)))))))))))))))))))))))))))) := by
  exact @SmallOrbit.Audit.check_accepted_raw

-- Independent literal expected type for SmallOrbit.Audit.check_accepted_small.
noncomputable def PartACanonical.Types.p0732 :
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
(∀ (_v8 : (@LT.lt.{0} (@Nat) (@instLTNat) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v8))) _v6)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat))))),
(@And (@LE.le.{0} (@Nat) (@instLENat) (@Pnp3.Models.Partial.tableLen (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
  (@Pnp4.Frontier.treeMCSPSearchProblem (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))))
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))
  (@Sigma.fst.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v9))) _v6))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)) (@Exists.{(0 + 1)} (@Nat) (fun (_v9 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v10 : (@Nat)) =>
(@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v2) _v9) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
  (@Nat) (@instAddNat)) _v1 _v2) _v9) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros?
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2
  (@Bool) _v3 _v4)) (@Option.some.{0} (@Nat) _v9)) (@And (@LE.le.{0} (@Nat) (@instLENat) _v10 (@HMul.hMul.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4096 : Nat) (@instOfNatNat (4096 : Nat)))
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))) (let _v12 : (∀ (_v12 : (@Nat)),
(@Option.{0} (@Bool))) := (@Body.extend (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Body.installedTape (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@SmallIngress.prepared _v1 _v2 (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)) _v3 _v4 _v9
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
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v9) (@OfNat.ofNat.{0} (@Nat)
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
(@And (∀ (_v13 : (@Nat)),
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v14))) _v6)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v14 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v14))) _v6))))),
(@Exists.{(0 + 1)} (@Nat) (fun (_v15 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v15 _v10) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SmallIngress.machine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SmallIngress.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v15 (@Pnp3.Complexity.Uniform.V1.initialConfig (@SmallIngress.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@SmallIngress.producer) (@Stream.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Stream.machine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Stream.paid (@Stream.Target.mode _v12 (@Stream.Target.cursor (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v9)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v13) (@HAdd.hAdd.{0, 0,
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v16))) _v6))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat
  (3 : Nat)))) _v11) (fun (_v16 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@Stream.Target.image _v12 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v9
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v17))) _v6)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v17 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v17))) _v6)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v9)) _v13 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@OfNat.ofNat.{0} (@Nat)
  (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Bool.true) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) _v16))))))))))) (@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@Stream.Target.cursor (@HAdd.hAdd.{0, 0, 0} (@Nat)
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v13))) _v6)))) (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)))) (fun (_v13 : (@LT.lt.{0} (@Nat) (@instLTNat) (@Stream.Target.cursor (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v13))) _v6)))) (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SmallIngress.machine)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SmallIngress.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v10 (@Pnp3.Complexity.Uniform.V1.initialConfig (@SmallIngress.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@SmallIngress.producer) (@Stream.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v14))) _v6)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v14))) _v6)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v14))) _v6)))) _v13) (fun (_v14 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@Stream.Target.image _v12 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v9
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v15))) _v6)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v9)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v15))) _v6))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v15))) _v6))) (@Bool.false) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) _v14)))))))))))))))))))))))))))) := by
  exact @SmallOrbit.Audit.check_accepted_small

-- Complete literal proposition for SmallOrbit.Audit.check_accepted_small; original proof reused.
theorem PartACanonical.Surface.m0442 :
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
(∀ (_v8 : (@LT.lt.{0} (@Nat) (@instLTNat) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v8))) _v6)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat))))),
(@And (@LE.le.{0} (@Nat) (@instLENat) (@Pnp3.Models.Partial.tableLen (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
  (@Pnp4.Frontier.treeMCSPSearchProblem (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))))
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))
  (@Sigma.fst.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v9))) _v6))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)) (@Exists.{(0 + 1)} (@Nat) (fun (_v9 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v10 : (@Nat)) =>
(@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v2) _v9) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
  (@Nat) (@instAddNat)) _v1 _v2) _v9) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros?
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2
  (@Bool) _v3 _v4)) (@Option.some.{0} (@Nat) _v9)) (@And (@LE.le.{0} (@Nat) (@instLENat) _v10 (@HMul.hMul.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4096 : Nat) (@instOfNatNat (4096 : Nat)))
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))) (let _v12 : (∀ (_v12 : (@Nat)),
(@Option.{0} (@Bool))) := (@Body.extend (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Body.installedTape (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@SmallIngress.prepared _v1 _v2 (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)) _v3 _v4 _v9
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
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v9) (@OfNat.ofNat.{0} (@Nat)
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
(@And (∀ (_v13 : (@Nat)),
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v14))) _v6)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v14 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v14))) _v6))))),
(@Exists.{(0 + 1)} (@Nat) (fun (_v15 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v15 _v10) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SmallIngress.machine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SmallIngress.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v15 (@Pnp3.Complexity.Uniform.V1.initialConfig (@SmallIngress.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@SmallIngress.producer) (@Stream.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Stream.machine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Stream.paid (@Stream.Target.mode _v12 (@Stream.Target.cursor (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v9)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v13) (@HAdd.hAdd.{0, 0,
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v16))) _v6))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat
  (3 : Nat)))) _v11) (fun (_v16 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@Stream.Target.image _v12 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v9
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v17))) _v6)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v17 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v17))) _v6)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v9)) _v13 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@OfNat.ofNat.{0} (@Nat)
  (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Bool.true) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) _v16))))))))))) (@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@Stream.Target.cursor (@HAdd.hAdd.{0, 0, 0} (@Nat)
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v13))) _v6)))) (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)))) (fun (_v13 : (@LT.lt.{0} (@Nat) (@instLTNat) (@Stream.Target.cursor (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v13))) _v6)))) (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SmallIngress.machine)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SmallIngress.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v10 (@Pnp3.Complexity.Uniform.V1.initialConfig (@SmallIngress.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@SmallIngress.producer) (@Stream.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v14))) _v6)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v14))) _v6)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v14))) _v6)))) _v13) (fun (_v14 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@Stream.Target.image _v12 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v9
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v15))) _v6)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v9)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v15))) _v6))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v15))) _v6))) (@Bool.false) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) _v14)))))))))))))))))))))))))))) := by
  exact @SmallOrbit.Audit.check_accepted_small

-- Independent literal expected type for SmallOrbit.Audit.check_image_eq_1.
noncomputable def PartACanonical.Types.p0733 :
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
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Stream.Target.image _v0 _v1 _v2 _v3 _v4 _v5 _v6 _v7 _v8) (let _v9 : (@Nat) :=
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))));
(let _v10 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v9 _v3) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat))));
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v9 _v8) (@LT.lt.{0} (@Nat) (@instLTNat) _v8
  _v10)) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) _v9 _v8) (@LT.lt.{0} (@Nat) (@instLTNat) _v8 _v10) (@Nat.decLt
  _v9 _v8) (@Nat.decLt _v8 _v10)) (@Option.some.{0} (@Bool) (@GetElem?.getElem!.{0, 0, 0} (@List.{0} (@Bool)) (@Nat)
  (@Bool) (fun (_v11 : (@List.{0} (@Bool))) =>
(fun (_v12 : (@Nat)) =>
(@LT.lt.{0} (@Nat) (@instLTNat) _v12 (@List.length.{0} (@Bool) _v11)))) (@List.instGetElem?NatLtLength.{0} (@Bool))
  (@instInhabitedBool) (@Body.iterBits (@List.replicate.{0} (@Bool) _v3 (@Bool.false)) _v5) (@HSub.hSub.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v8))) (@ite.{(0 + 1)} (@Option.{0}
  (@Bool)) (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v10 _v8) (@LE.le.{0} (@Nat) (@instLENat) _v8 (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 _v6))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat)
  _v10 _v8) (@LE.le.{0} (@Nat) (@instLENat) _v8 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v10 _v6)) (@Nat.decLt _v10 _v8) (@Nat.decLe _v8 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 _v6))) (@Option.some.{0} (@Bool) (@Bool.true)) (@ite.{(0 + 1)} (@Option.{0}
  (@Bool)) (@And (@Eq.{(0 + 1)} (@Bool) _v7 (@Bool.true)) (@And (@Eq.{(0 + 1)} (@Nat) _v8 (@Stream.Target.cursor _v4 _v1
  _v5)) (@LT.lt.{0} (@Nat) (@instLTNat) _v8 _v1))) (@instDecidableAnd (@Eq.{(0 + 1)} (@Bool) _v7 (@Bool.true)) (@And
  (@Eq.{(0 + 1)} (@Nat) _v8 (@Stream.Target.cursor _v4 _v1 _v5)) (@LT.lt.{0} (@Nat) (@instLTNat) _v8 _v1))
  (@instDecidableEqBool _v7 (@Bool.true)) (@instDecidableAnd (@Eq.{(0 + 1)} (@Nat) _v8 (@Stream.Target.cursor _v4 _v1
  _v5)) (@LT.lt.{0} (@Nat) (@instLTNat) _v8 _v1) (@instDecidableEqNat _v8 (@Stream.Target.cursor _v4 _v1 _v5)) (@Nat.decLt
  _v8 _v1))) (@Option.none.{0} (@Bool)) (@_v0 _v8)))))))))))))))) := by
  exact @SmallOrbit.Audit.check_image_eq_1

-- Complete literal proposition for SmallOrbit.Audit.check_image_eq_1; original proof reused.
theorem PartACanonical.Surface.m0443 :
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
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Stream.Target.image _v0 _v1 _v2 _v3 _v4 _v5 _v6 _v7 _v8) (let _v9 : (@Nat) :=
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))));
(let _v10 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v9 _v3) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat))));
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v9 _v8) (@LT.lt.{0} (@Nat) (@instLTNat) _v8
  _v10)) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) _v9 _v8) (@LT.lt.{0} (@Nat) (@instLTNat) _v8 _v10) (@Nat.decLt
  _v9 _v8) (@Nat.decLt _v8 _v10)) (@Option.some.{0} (@Bool) (@GetElem?.getElem!.{0, 0, 0} (@List.{0} (@Bool)) (@Nat)
  (@Bool) (fun (_v11 : (@List.{0} (@Bool))) =>
(fun (_v12 : (@Nat)) =>
(@LT.lt.{0} (@Nat) (@instLTNat) _v12 (@List.length.{0} (@Bool) _v11)))) (@List.instGetElem?NatLtLength.{0} (@Bool))
  (@instInhabitedBool) (@Body.iterBits (@List.replicate.{0} (@Bool) _v3 (@Bool.false)) _v5) (@HSub.hSub.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v8))) (@ite.{(0 + 1)} (@Option.{0}
  (@Bool)) (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v10 _v8) (@LE.le.{0} (@Nat) (@instLENat) _v8 (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 _v6))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat)
  _v10 _v8) (@LE.le.{0} (@Nat) (@instLENat) _v8 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v10 _v6)) (@Nat.decLt _v10 _v8) (@Nat.decLe _v8 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 _v6))) (@Option.some.{0} (@Bool) (@Bool.true)) (@ite.{(0 + 1)} (@Option.{0}
  (@Bool)) (@And (@Eq.{(0 + 1)} (@Bool) _v7 (@Bool.true)) (@And (@Eq.{(0 + 1)} (@Nat) _v8 (@Stream.Target.cursor _v4 _v1
  _v5)) (@LT.lt.{0} (@Nat) (@instLTNat) _v8 _v1))) (@instDecidableAnd (@Eq.{(0 + 1)} (@Bool) _v7 (@Bool.true)) (@And
  (@Eq.{(0 + 1)} (@Nat) _v8 (@Stream.Target.cursor _v4 _v1 _v5)) (@LT.lt.{0} (@Nat) (@instLTNat) _v8 _v1))
  (@instDecidableEqBool _v7 (@Bool.true)) (@instDecidableAnd (@Eq.{(0 + 1)} (@Nat) _v8 (@Stream.Target.cursor _v4 _v1
  _v5)) (@LT.lt.{0} (@Nat) (@instLTNat) _v8 _v1) (@instDecidableEqNat _v8 (@Stream.Target.cursor _v4 _v1 _v5)) (@Nat.decLt
  _v8 _v1))) (@Option.none.{0} (@Bool)) (@_v0 _v8)))))))))))))))) := by
  exact @SmallOrbit.Audit.check_image_eq_1

-- Independent literal expected type for SmallOrbit.Audit.check_original_accepted_raw.
noncomputable def PartACanonical.Types.p0734 :
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
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)) (@Exists.{(0 + 1)} (@Nat) (fun (_v7 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v8 : (@Nat)) =>
(@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v2) _v7) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
  (@Pnp4.Frontier.treeMCSPSearchProblem (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))))
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))
  (@Sigma.fst.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v9))) _v6))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)))) (fun (_v9 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v2) _v7) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
  (@Pnp4.Frontier.treeMCSPSearchProblem (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))))
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))
  (@Sigma.fst.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v9))) _v6))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros?
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2
  (@Bool) _v3 _v4)) (@Option.some.{0} (@Nat) _v7)) (@And (@LE.le.{0} (@Nat) (@instLENat) _v8 (@HMul.hMul.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4096 : Nat) (@instOfNatNat (4096 : Nat)))
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))) (let _v10 : (∀ (_v10 : (@Nat)),
(@Option.{0} (@Bool))) := (@Body.extend (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Body.installedTape (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@SmallIngress.prepared _v1 _v2 (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)) _v3 _v4 _v7
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v10))) _v6))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v7) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat)))) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v10))) _v6))));
(@And (∀ (_v11 : (@Nat)),
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) _v11 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat)
  (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v12))) _v6))))),
(@Exists.{(0 + 1)} (@Nat) (fun (_v13 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v13 _v8) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SmallIngress.machine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SmallIngress.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v13 (@Pnp3.Complexity.Uniform.V1.initialConfig (@SmallIngress.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@SmallIngress.producer) (@Stream.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Stream.machine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Stream.paid (@Stream.Target.mode _v10 (@Stream.Target.cursor (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v7)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v11) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2))) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v7)
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
  (3 : Nat)))) _v9) (fun (_v14 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@Stream.Target.image _v10 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v7
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v15))) _v6)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v7)) _v11 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 (@OfNat.ofNat.{0} (@Nat)
  (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Bool.true) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) _v14))))))))))) (@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@Stream.Target.cursor (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v7)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  _v2) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v11))) _v6)))) (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)))) (fun (_v11 : (@LT.lt.{0} (@Nat) (@instLTNat) (@Stream.Target.cursor (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v7)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v11))) _v6)))) (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SmallIngress.machine)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SmallIngress.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v8 (@Pnp3.Complexity.Uniform.V1.initialConfig (@SmallIngress.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@SmallIngress.producer) (@Stream.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Stream.machine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Stream.q (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Stream.Target.cursor (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v7)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v12))) _v6)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)) (@instDecidableEqNat (@Stream.Target.cursor (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v7)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v12))) _v6)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)) (@OfNat.ofNat.{0} (@Nat) (57 : Nat) (@instOfNatNat (57 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (58 : Nat) (@instOfNatNat (58 : Nat))))) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@Stream.Target.cursor (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v7)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0}
  (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v12))) _v6)))) _v11) (fun (_v12 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@Stream.Target.image _v10 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v7
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v13))) _v6)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v7)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v13))) _v6))) (@Bool.false) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) _v12)))))))))))))))))))))))))))) := by
  exact @SmallOrbit.Audit.check_original_accepted_raw

-- Complete literal proposition for SmallOrbit.Audit.check_original_accepted_raw; original proof reused.
theorem PartACanonical.Surface.m0444 :
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
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)) (@Exists.{(0 + 1)} (@Nat) (fun (_v7 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v8 : (@Nat)) =>
(@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v2) _v7) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
  (@Pnp4.Frontier.treeMCSPSearchProblem (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))))
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))
  (@Sigma.fst.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v9))) _v6))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)))) (fun (_v9 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v2) _v7) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
  (@Pnp4.Frontier.treeMCSPSearchProblem (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))))
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))
  (@Sigma.fst.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v9))) _v6))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros?
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2
  (@Bool) _v3 _v4)) (@Option.some.{0} (@Nat) _v7)) (@And (@LE.le.{0} (@Nat) (@instLENat) _v8 (@HMul.hMul.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4096 : Nat) (@instOfNatNat (4096 : Nat)))
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))) (let _v10 : (∀ (_v10 : (@Nat)),
(@Option.{0} (@Bool))) := (@Body.extend (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Body.installedTape (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@SmallIngress.prepared _v1 _v2 (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)) _v3 _v4 _v7
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v10))) _v6))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v7) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat)))) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v10))) _v6))));
(@And (∀ (_v11 : (@Nat)),
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) _v11 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat)
  (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v12))) _v6))))),
(@Exists.{(0 + 1)} (@Nat) (fun (_v13 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v13 _v8) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SmallIngress.machine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SmallIngress.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v13 (@Pnp3.Complexity.Uniform.V1.initialConfig (@SmallIngress.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@SmallIngress.producer) (@Stream.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Stream.machine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Stream.paid (@Stream.Target.mode _v10 (@Stream.Target.cursor (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v7)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v11) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2))) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v7)
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
  (3 : Nat)))) _v9) (fun (_v14 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@Stream.Target.image _v10 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v7
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v15))) _v6)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v7)) _v11 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 (@OfNat.ofNat.{0} (@Nat)
  (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Bool.true) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) _v14))))))))))) (@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@Stream.Target.cursor (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v7)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  _v2) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v11))) _v6)))) (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)))) (fun (_v11 : (@LT.lt.{0} (@Nat) (@instLTNat) (@Stream.Target.cursor (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v7)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v11))) _v6)))) (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SmallIngress.machine)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SmallIngress.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v8 (@Pnp3.Complexity.Uniform.V1.initialConfig (@SmallIngress.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@SmallIngress.producer) (@Stream.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Stream.machine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Stream.q (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Stream.Target.cursor (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v7)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v12))) _v6)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)) (@instDecidableEqNat (@Stream.Target.cursor (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v7)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v12))) _v6)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)) (@OfNat.ofNat.{0} (@Nat) (57 : Nat) (@instOfNatNat (57 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (58 : Nat) (@instOfNatNat (58 : Nat))))) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@Stream.Target.cursor (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v7)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0}
  (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v12))) _v6)))) _v11) (fun (_v12 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@Stream.Target.image _v10 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v7
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v13))) _v6)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v7)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v13))) _v6))) (@Bool.false) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) _v12)))))))))))))))))))))))))))) := by
  exact @SmallOrbit.Audit.check_original_accepted_raw

-- Independent literal expected type for SmallOrbit.Audit.check_prepared_eq_1.
noncomputable def PartACanonical.Types.p0735 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v0)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  _v2))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@SmallIngress.prepared _v0 _v1 _v2 _v3 _v4 _v5 _v6 _v7) (@ite.{(0 + 1)}
  (@Option.{0} (@Bool)) (@And (@Eq.{(0 + 1)} (@Nat) _v6 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) _v2) _v7) (@OfNat.ofNat.{0} (@Nat) (7 : Nat)
  (@instOfNatNat (7 : Nat))))) (@instDecidableAnd (@Eq.{(0 + 1)} (@Nat) _v6 (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) _v2) _v7) (@OfNat.ofNat.{0} (@Nat) (7 : Nat)
  (@instOfNatNat (7 : Nat)))) (@instDecidableEqNat _v6 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@instDecidableEqNat (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) _v2) _v7) (@OfNat.ofNat.{0} (@Nat) (7 : Nat)
  (@instOfNatNat (7 : Nat))))) (@Option.none.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.countdownTape
  _v0 _v1 _v2 _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v6 _v7))))))))))) := by
  exact @SmallOrbit.Audit.check_prepared_eq_1

-- Complete literal proposition for SmallOrbit.Audit.check_prepared_eq_1; original proof reused.
theorem PartACanonical.Surface.m0445 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v0)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1)
  _v2))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@SmallIngress.prepared _v0 _v1 _v2 _v3 _v4 _v5 _v6 _v7) (@ite.{(0 + 1)}
  (@Option.{0} (@Bool)) (@And (@Eq.{(0 + 1)} (@Nat) _v6 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) _v2) _v7) (@OfNat.ofNat.{0} (@Nat) (7 : Nat)
  (@instOfNatNat (7 : Nat))))) (@instDecidableAnd (@Eq.{(0 + 1)} (@Nat) _v6 (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) _v2) _v7) (@OfNat.ofNat.{0} (@Nat) (7 : Nat)
  (@instOfNatNat (7 : Nat)))) (@instDecidableEqNat _v6 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@instDecidableEqNat (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v0 _v1) _v2) _v7) (@OfNat.ofNat.{0} (@Nat) (7 : Nat)
  (@instOfNatNat (7 : Nat))))) (@Option.none.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.countdownTape
  _v0 _v1 _v2 _v3 _v4 _v5 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v6 _v7))))))))))) := by
  exact @SmallOrbit.Audit.check_prepared_eq_1

-- Independent literal expected type for SmallOrbit.Audit.check_small_header_physical.
noncomputable def PartACanonical.Types.p0736 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v2)),
(∀ (_v5 : (@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v1
  _v2 _v3 _v4) (@Bool.true))),
(∀ {_v6 : (@Sigma.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v6))))},
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
(∀ (_v8 : (@LT.lt.{0} (@Nat) (@instLTNat) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v8))) _v6)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat))))),
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros?
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2
  (@Bool) _v3 _v4)) (@Option.some.{0} (@Nat) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat)
  (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v9))) _v6)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0
  : Nat)))) (@instDecidableEqNat (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v9))) _v6)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0
  : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))))) (@And (@LE.le.{0} (@Nat) (@instLENat) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat)
  (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v9))) _v6)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0
  : Nat)))) (@instDecidableEqNat (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v9))) _v6)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0
  : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2))
  (@And (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.physicalSymbol
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2
  (@Bool) _v3 _v4) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))) (@Option.some.{0} (@Bool) (@BEq.beq.{0}
  (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
  (@Pnp4.Frontier.treeMCSPSearchProblem (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))))
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))
  (@Sigma.fst.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v9))) _v6)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0
  : Nat)))))) (@And (∀ (_v9 : (@Ne.{(0 + 1)} (@Nat) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
  (@Pnp4.Frontier.treeMCSPSearchProblem (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))))
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))
  (@Sigma.fst.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v9))) _v6)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0
  : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.physicalSymbol (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v3 _v4)
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))) (@Option.some.{0} (@Bool) (@Bool.true)))) (∀ (_v9 :
  (@Ne.{(0 + 1)} (@Nat) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v9))) _v6)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0
  : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.physicalSymbol (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v3 _v4)
  (@OfNat.ofNat.{0} (@Nat) (10 : Nat) (@instOfNatNat (10 : Nat)))) (@Option.some.{0} (@Bool) (@BEq.beq.{0} (@Nat)
  (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v10))) _v6)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2
  : Nat)))))))))))))))))))) := by
  exact @SmallOrbit.Audit.check_small_header_physical

-- Complete literal proposition for SmallOrbit.Audit.check_small_header_physical; original proof reused.
theorem PartACanonical.Surface.m0446 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v2)),
(∀ (_v5 : (@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v1
  _v2 _v3 _v4) (@Bool.true))),
(∀ {_v6 : (@Sigma.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v6))))},
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
(∀ (_v8 : (@LT.lt.{0} (@Nat) (@instLTNat) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v8))) _v6)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat))))),
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros?
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2
  (@Bool) _v3 _v4)) (@Option.some.{0} (@Nat) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat)
  (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v9))) _v6)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0
  : Nat)))) (@instDecidableEqNat (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v9))) _v6)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0
  : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))))) (@And (@LE.le.{0} (@Nat) (@instLENat) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat)
  (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v9))) _v6)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0
  : Nat)))) (@instDecidableEqNat (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v9))) _v6)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0
  : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2))
  (@And (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.physicalSymbol
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2
  (@Bool) _v3 _v4) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))) (@Option.some.{0} (@Bool) (@BEq.beq.{0}
  (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
  (@Pnp4.Frontier.treeMCSPSearchProblem (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))))
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))
  (@Sigma.fst.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v9))) _v6)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0
  : Nat)))))) (@And (∀ (_v9 : (@Ne.{(0 + 1)} (@Nat) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
  (@Pnp4.Frontier.treeMCSPSearchProblem (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))))
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))
  (@Sigma.fst.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v9))) _v6)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0
  : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.physicalSymbol (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v3 _v4)
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))) (@Option.some.{0} (@Bool) (@Bool.true)))) (∀ (_v9 :
  (@Ne.{(0 + 1)} (@Nat) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v9))) _v6)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0
  : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.physicalSymbol (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v3 _v4)
  (@OfNat.ofNat.{0} (@Nat) (10 : Nat) (@instOfNatNat (10 : Nat)))) (@Option.some.{0} (@Bool) (@BEq.beq.{0} (@Nat)
  (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v10))) _v6)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2
  : Nat)))))))))))))))))))) := by
  exact @SmallOrbit.Audit.check_small_header_physical

-- Independent literal expected type for SmallOrbit.Audit.pin_AcceptedOrbit.
noncomputable def PartACanonical.Types.p0737 :
(∀ (_v0 : (@Nat)),
(Sort 0)) := by
  exact @SmallOrbit.Audit.pin_AcceptedOrbit

-- Independent literal expected type for SmallOrbit.Audit.pin_SmallAcceptedOrbit.
noncomputable def PartACanonical.Types.p0738 :
(∀ (_v0 : (@Nat)),
(Sort 0)) := by
  exact @SmallOrbit.Audit.pin_SmallAcceptedOrbit

-- Independent literal expected type for SmallOrbit.Target.AcceptedOrbit.
noncomputable def PartACanonical.Types.p0739 :
(∀ (_v0 : (@Nat)),
(Sort 0)) := by
  exact @SmallOrbit.Target.AcceptedOrbit

-- Independent literal expected type for SmallOrbit.Target.SmallAcceptedOrbit.
noncomputable def PartACanonical.Types.p0740 :
(∀ (_v0 : (@Nat)),
(Sort 0)) := by
  exact @SmallOrbit.Target.SmallAcceptedOrbit

-- Independent literal expected type for SmallOrbit.accepted_raw.
noncomputable def PartACanonical.Types.p0741 :
(∀ (_v0 : (@Nat)),
(@SmallOrbit.Target.AcceptedOrbit _v0)) := by
  exact @SmallOrbit.accepted_raw

-- Complete literal proposition for SmallOrbit.accepted_raw; original proof reused.
theorem PartACanonical.Surface.m0447 :
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
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)) (@Exists.{(0 + 1)} (@Nat) (fun (_v7 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v8 : (@Nat)) =>
(@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v2) _v7) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
  (@Pnp4.Frontier.treeMCSPSearchProblem (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))))
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))
  (@Sigma.fst.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v9))) _v6))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)))) (fun (_v9 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v2) _v7) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
  (@Pnp4.Frontier.treeMCSPSearchProblem (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))))
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))
  (@Sigma.fst.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v9))) _v6))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros?
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2
  (@Bool) _v3 _v4)) (@Option.some.{0} (@Nat) _v7)) (@And (@LE.le.{0} (@Nat) (@instLENat) _v8 (@HMul.hMul.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4096 : Nat) (@instOfNatNat (4096 : Nat)))
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))) (let _v10 : (∀ (_v10 : (@Nat)),
(@Option.{0} (@Bool))) := (@Body.extend (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Body.installedTape (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@SmallIngress.prepared _v1 _v2 (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)) _v3 _v4 _v7
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v10))) _v6))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v7) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat)))) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v10))) _v6))));
(@And (∀ (_v11 : (@Nat)),
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) _v11 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat)
  (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v12))) _v6))))),
(@Exists.{(0 + 1)} (@Nat) (fun (_v13 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v13 _v8) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SmallIngress.machine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SmallIngress.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v13 (@Pnp3.Complexity.Uniform.V1.initialConfig (@SmallIngress.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@SmallIngress.producer) (@Stream.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Stream.machine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Stream.paid (@Stream.Target.mode _v10 (@Stream.Target.cursor (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v7)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v11) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2))) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v7)
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
  (3 : Nat)))) _v9) (fun (_v14 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@Stream.Target.image _v10 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v7
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v15))) _v6)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v7)) _v11 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 (@OfNat.ofNat.{0} (@Nat)
  (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Bool.true) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) _v14))))))))))) (@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@Stream.Target.cursor (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v7)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  _v2) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v11))) _v6)))) (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)))) (fun (_v11 : (@LT.lt.{0} (@Nat) (@instLTNat) (@Stream.Target.cursor (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v7)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v11))) _v6)))) (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SmallIngress.machine)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SmallIngress.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v8 (@Pnp3.Complexity.Uniform.V1.initialConfig (@SmallIngress.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@SmallIngress.producer) (@Stream.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Stream.machine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Stream.q (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Stream.Target.cursor (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v7)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v12))) _v6)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)) (@instDecidableEqNat (@Stream.Target.cursor (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v7)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v12))) _v6)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)) (@OfNat.ofNat.{0} (@Nat) (57 : Nat) (@instOfNatNat (57 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (58 : Nat) (@instOfNatNat (58 : Nat))))) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@Stream.Target.cursor (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v7)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0}
  (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v12))) _v6)))) _v11) (fun (_v12 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@Stream.Target.image _v10 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v7
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v13))) _v6)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v7)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v13))) _v6))) (@Bool.false) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) _v12)))))))))))))))))))))))))))) := by
  exact @SmallOrbit.accepted_raw

-- Independent literal expected type for SmallOrbit.accepted_small.
noncomputable def PartACanonical.Types.p0742 :
(∀ (_v0 : (@Nat)),
(@SmallOrbit.Target.SmallAcceptedOrbit _v0)) := by
  exact @SmallOrbit.accepted_small

-- Complete literal proposition for SmallOrbit.accepted_small; original proof reused.
theorem PartACanonical.Surface.m0448 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v2)),
(∀ (_v5 : (@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v1
  _v2 _v3 _v4) (@Bool.true))),
(∀ (_v6 : (@AcceptedBody.Parsed _v0)),
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
(∀ (_v8 : (@LT.lt.{0} (@Nat) (@instLTNat) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v8))) _v6)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat))))),
(@And (@LE.le.{0} (@Nat) (@instLENat) (@Pnp3.Models.Partial.tableLen (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
  (@Pnp4.Frontier.treeMCSPSearchProblem (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))))
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))
  (@Sigma.fst.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v9))) _v6))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)) (@Exists.{(0 + 1)} (@Nat) (fun (_v9 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v10 : (@Nat)) =>
(@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v2) _v9) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
  (@Nat) (@instAddNat)) _v1 _v2) _v9) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros?
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2
  (@Bool) _v3 _v4)) (@Option.some.{0} (@Nat) _v9)) (@And (@LE.le.{0} (@Nat) (@instLENat) _v10 (@HMul.hMul.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4096 : Nat) (@instOfNatNat (4096 : Nat)))
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))) (let _v12 : (∀ (_v12 : (@Nat)),
(@Option.{0} (@Bool))) := (@Body.extend (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Body.installedTape (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@SmallIngress.prepared _v1 _v2 (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)) _v3 _v4 _v9
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
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v9) (@OfNat.ofNat.{0} (@Nat)
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
(@And (∀ (_v13 : (@Nat)),
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v14))) _v6)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v14 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v14))) _v6))))),
(@Exists.{(0 + 1)} (@Nat) (fun (_v15 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v15 _v10) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SmallIngress.machine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SmallIngress.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v15 (@Pnp3.Complexity.Uniform.V1.initialConfig (@SmallIngress.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@SmallIngress.producer) (@Stream.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Stream.machine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Stream.paid (@Stream.Target.mode _v12 (@Stream.Target.cursor (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v9)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v13) (@HAdd.hAdd.{0, 0,
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v16))) _v6))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat
  (3 : Nat)))) _v11) (fun (_v16 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@Stream.Target.image _v12 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v9
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v17))) _v6)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v17 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v17))) _v6)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v9)) _v13 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@OfNat.ofNat.{0} (@Nat)
  (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Bool.true) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) _v16))))))))))) (@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@Stream.Target.cursor (@HAdd.hAdd.{0, 0, 0} (@Nat)
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v13))) _v6)))) (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)))) (fun (_v13 : (@LT.lt.{0} (@Nat) (@instLTNat) (@Stream.Target.cursor (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v13))) _v6)))) (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SmallIngress.machine)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SmallIngress.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v10 (@Pnp3.Complexity.Uniform.V1.initialConfig (@SmallIngress.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@SmallIngress.producer) (@Stream.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v14))) _v6)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v14))) _v6)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v14))) _v6)))) _v13) (fun (_v14 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@Stream.Target.image _v12 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v9
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v15))) _v6)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v9)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v15))) _v6))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v15))) _v6))) (@Bool.false) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) _v14)))))))))))))))))))))))))))) := by
  exact @SmallOrbit.accepted_small

-- Independent literal expected type for SmallOrbit.original_accepted_raw.
noncomputable def PartACanonical.Types.p0743 :
(∀ (_v0 : (@Nat)),
(@SmallIngress.Target.AcceptedOrbit _v0)) := by
  exact @SmallOrbit.original_accepted_raw

-- Complete literal proposition for SmallOrbit.original_accepted_raw; original proof reused.
theorem PartACanonical.Surface.m0449 :
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
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)) (@Exists.{(0 + 1)} (@Nat) (fun (_v7 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v8 : (@Nat)) =>
(@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v2) _v7) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
  (@Pnp4.Frontier.treeMCSPSearchProblem (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))))
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))
  (@Sigma.fst.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v9))) _v6))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)))) (fun (_v9 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v2) _v7) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
  (@Pnp4.Frontier.treeMCSPSearchProblem (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))))
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))
  (@Sigma.fst.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v9))) _v6))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros?
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2
  (@Bool) _v3 _v4)) (@Option.some.{0} (@Nat) _v7)) (@And (@LE.le.{0} (@Nat) (@instLENat) _v8 (@HMul.hMul.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4096 : Nat) (@instOfNatNat (4096 : Nat)))
  (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))) (let _v10 : (∀ (_v10 : (@Nat)),
(@Option.{0} (@Bool))) := (@Body.extend (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Body.installedTape (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@SmallIngress.prepared _v1 _v2 (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)) _v3 _v4 _v7
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v10))) _v6))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v7) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat)))) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v10))) _v6))));
(@And (∀ (_v11 : (@Nat)),
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) _v11 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat)
  (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v12))) _v6))))),
(@Exists.{(0 + 1)} (@Nat) (fun (_v13 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v13 _v8) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@SmallIngress.machine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SmallIngress.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v13 (@Pnp3.Complexity.Uniform.V1.initialConfig (@SmallIngress.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@SmallIngress.producer) (@Stream.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Stream.machine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Stream.paid (@Stream.Target.mode _v10 (@Stream.Target.cursor (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v7)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v11) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2))) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v7)
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
  (3 : Nat)))) _v9) (fun (_v14 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@Stream.Target.image _v10 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v7
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v15))) _v6)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v7)) _v11 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 (@OfNat.ofNat.{0} (@Nat)
  (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Bool.true) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) _v14))))))))))) (@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@Stream.Target.cursor (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v7)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  _v2) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v11))) _v6)))) (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)))) (fun (_v11 : (@LT.lt.{0} (@Nat) (@instLTNat) (@Stream.Target.cursor (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v7)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v11))) _v6)))) (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SmallIngress.machine)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@SmallIngress.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v8 (@Pnp3.Complexity.Uniform.V1.initialConfig (@SmallIngress.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@SmallIngress.producer) (@Stream.machine)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Stream.machine))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Stream.q (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) (@Stream.Target.cursor (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v7)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v12))) _v6)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)) (@instDecidableEqNat (@Stream.Target.cursor (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v7)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v12))) _v6)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)) (@OfNat.ofNat.{0} (@Nat) (57 : Nat) (@instOfNatNat (57 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (58 : Nat) (@instOfNatNat (58 : Nat))))) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) (@Stream.Target.cursor (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v7)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0}
  (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v12))) _v6)))) _v11) (fun (_v12 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))))) =>
(@Stream.Target.image _v10 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v7
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v13))) _v6)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v7)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v13))) _v6))) (@Bool.false) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2))) _v12)))))))))))))))))))))))))))) := by
  exact @SmallOrbit.original_accepted_raw

-- Independent literal expected type for SmallOrbit.small_header_physical.
noncomputable def PartACanonical.Types.p0744 :
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
(∀ (_v8 : (@LT.lt.{0} (@Nat) (@instLTNat) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v8))) _v6)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat))))),
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros?
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2
  (@Bool) _v3 _v4)) (@Option.some.{0} (@Nat) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat)
  (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v9))) _v6)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0
  : Nat)))) (@instDecidableEqNat (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v9))) _v6)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0
  : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))))) (@And (@LE.le.{0} (@Nat) (@instLENat) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat)
  (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v9))) _v6)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0
  : Nat)))) (@instDecidableEqNat (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v9))) _v6)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0
  : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2))
  (@And (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.physicalSymbol
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2
  (@Bool) _v3 _v4) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))) (@Option.some.{0} (@Bool) (@BEq.beq.{0}
  (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
  (@Pnp4.Frontier.treeMCSPSearchProblem (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))))
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))
  (@Sigma.fst.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v9))) _v6)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0
  : Nat)))))) (@And (∀ (_v9 : (@Ne.{(0 + 1)} (@Nat) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
  (@Pnp4.Frontier.treeMCSPSearchProblem (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))))
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))
  (@Sigma.fst.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v9))) _v6)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0
  : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.physicalSymbol (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v3 _v4)
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))) (@Option.some.{0} (@Bool) (@Bool.true)))) (∀ (_v9 :
  (@Ne.{(0 + 1)} (@Nat) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v9))) _v6)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0
  : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.physicalSymbol (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v3 _v4)
  (@OfNat.ofNat.{0} (@Nat) (10 : Nat) (@instOfNatNat (10 : Nat)))) (@Option.some.{0} (@Bool) (@BEq.beq.{0} (@Nat)
  (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v10))) _v6)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2
  : Nat)))))))))))))))))))) := by
  exact @SmallOrbit.small_header_physical

-- Complete literal proposition for SmallOrbit.small_header_physical; original proof reused.
theorem PartACanonical.Surface.m0450 :
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
(∀ (_v8 : (@LT.lt.{0} (@Nat) (@instLTNat) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v8))) _v6)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat))))),
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros?
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2
  (@Bool) _v3 _v4)) (@Option.some.{0} (@Nat) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat)
  (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v9))) _v6)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0
  : Nat)))) (@instDecidableEqNat (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v9))) _v6)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0
  : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))))) (@And (@LE.le.{0} (@Nat) (@instLENat) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat)
  (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v9))) _v6)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0
  : Nat)))) (@instDecidableEqNat (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v9))) _v6)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0
  : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2))
  (@And (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.physicalSymbol
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2
  (@Bool) _v3 _v4) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))) (@Option.some.{0} (@Bool) (@BEq.beq.{0}
  (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
  (@Pnp4.Frontier.treeMCSPSearchProblem (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))))
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))
  (@Sigma.fst.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v9))) _v6)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0
  : Nat)))))) (@And (∀ (_v9 : (@Ne.{(0 + 1)} (@Nat) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
  (@Pnp4.Frontier.treeMCSPSearchProblem (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))))
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0))
  (@Sigma.fst.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v9))) _v6)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0
  : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.physicalSymbol (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v3 _v4)
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))) (@Option.some.{0} (@Bool) (@Bool.true)))) (∀ (_v9 :
  (@Ne.{(0 + 1)} (@Nat) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v9))) _v6)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0
  : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.FixedContentTagGate.physicalSymbol (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Fin.append.{(0 + 1)} _v1 _v2 (@Bool) _v3 _v4)
  (@OfNat.ofNat.{0} (@Nat) (10 : Nat) (@instOfNatNat (10 : Nat)))) (@Option.some.{0} (@Bool) (@BEq.beq.{0} (@Nat)
  (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v10))) _v6)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2
  : Nat)))))))))))))))))))) := by
  exact @SmallOrbit.small_header_physical

-- Independent literal expected type for StandardTMBridgeClosure.Audit.pin_Raw.
noncomputable def PartACanonical.Types.p0745 :
(∀ (_v0 : (@Nat)),
(Sort 0)) := by
  exact @StandardTMBridgeClosure.Audit.pin_Raw

-- Independent literal expected type for StandardTMBridgeClosure.Audit.pin_Represents.
noncomputable def PartACanonical.Types.p0746 :
(∀ (_v0 : (@Pnp3.Complexity.Uniform.V1.UniformTM)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2)),
(∀ (_v4 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))),
(Sort 0)))))) := by
  exact @StandardTMBridgeClosure.Audit.pin_Represents

-- Independent literal expected type for StandardTMBridgeClosure.Audit.pin_Simulation.
noncomputable def PartACanonical.Types.p0747 :
(∀ (_v0 : (@Pnp3.Complexity.Uniform.V1.UniformTM)),
(Sort 0)) := by
  exact @StandardTMBridgeClosure.Audit.pin_Simulation

-- Independent literal expected type for StandardTMBridgeClosure.Audit.pin_Source.
noncomputable def PartACanonical.Types.p0748 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (∀ (_v2 : (@Fin _v1)),
(@Bool))),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(Sort 0)))))) := by
  exact @StandardTMBridgeClosure.Audit.pin_Source

-- Independent literal expected type for StandardTMBridgeClosure.Audit.pin_compile.
noncomputable def PartACanonical.Types.p0749 :
(∀ (_v0 : (@Pnp3.Complexity.Uniform.V1.UniformTM)),
(@Turing.TM0.Machine.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedOption.{0} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))))) := by
  exact @StandardTMBridgeClosure.Audit.pin_compile

-- Independent literal expected type for StandardTMBridgeClosure.Audit.pin_degree.
noncomputable def PartACanonical.Types.p0750 :
(∀ (_v0 : (@Nat)),
(@Nat)) := by
  exact @StandardTMBridgeClosure.Audit.pin_degree

-- Independent literal expected type for StandardTMBridgeClosure.Audit.pin_encode.
noncomputable def PartACanonical.Types.p0751 :
(∀ (_v0 : (@List.{0} (@Bool))),
(@List.{0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))))) := by
  exact @StandardTMBridgeClosure.Audit.pin_encode

-- Independent literal expected type for StandardTMBridgeClosure.Audit.pin_steps.
noncomputable def PartACanonical.Types.p0752 :
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
  exact @StandardTMBridgeClosure.Audit.pin_steps

-- Independent literal expected type for StandardTMBridgeClosure.Represents.
noncomputable def PartACanonical.Types.p0753 :
(∀ (_v0 : (@Pnp3.Complexity.Uniform.V1.UniformTM)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0) _v1 _v2)),
(∀ (_v4 : (@Turing.TM0.Cfg.{0, 0} (@Prod.{0, 0} (@Bool) (@Option.{0} (@Bool))) (@Option.{0} (@Prod.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount _v0)) (@Fin (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@instInhabitedProd.{0, 0} (@Bool) (@Option.{0} (@Bool)) (@instInhabitedBool) (@instInhabitedOption.{0}
  (@Bool))))),
(Sort 0)))))) := by
  exact @StandardTMBridgeClosure.Represents

-- Independent literal expected type for StandardTMBridgeClosure.Target.Raw.
noncomputable def PartACanonical.Types.p0754 :
(∀ (_v0 : (@Nat)),
(Sort 0)) := by
  exact @StandardTMBridgeClosure.Target.Raw

-- Independent literal expected type for StandardTMBridgeClosure.Target.Simulation.
noncomputable def PartACanonical.Types.p0755 :
(∀ (_v0 : (@Pnp3.Complexity.Uniform.V1.UniformTM)),
(Sort 0)) := by
  exact @StandardTMBridgeClosure.Target.Simulation
