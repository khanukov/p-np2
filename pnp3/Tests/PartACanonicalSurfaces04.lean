import Tests.PartACanonicalABI
import Tests.PartAG2InterfaceTests

/-! Infrastructure: mechanical literal restatements of this exact original API.
Proof terms are reused; these are not independently authored correctness proofs.
Type pins, theorem mirrors and direct roots remain separate manifests. -/
set_option autoImplicit false

-- Independent literal expected type for Body.round_path.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0187 :
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
-- Complete literal proposition for Body.round_path; original proof reused.
theorem PartACanonical.Surface.m0112 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@List.{0} (@Bool))),
(∀ (_v3 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v0 _v1) (@Option.none.{0} (@Bool)))),
(∀ (_v4 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@List.length.{0}
  (@Bool) _v2)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Option.none.{0} (@Bool)))),
(∀ (_v5 : (∀ (_v5 : (@Nat)),
(∀ (_v6 : (@LT.lt.{0} (@Nat) (@instLTNat) _v5 (@List.length.{0} (@Bool) _v2))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v0 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@List.length.{0}
  (@Bool) _v2)) _v5)) (@Option.some.{0} (@Bool) (@GetElem?.getElem!.{0, 0, 0} (@List.{0} (@Bool)) (@Nat) (@Bool) (fun (_v7
  : (@List.{0} (@Bool))) =>
(fun (_v8 : (@Nat)) =>
(@LT.lt.{0} (@Nat) (@instLTNat) _v8 (@List.length.{0} (@Bool) _v7)))) (@List.instGetElem?NatLtLength.{0} (@Bool))
  (@instInhabitedBool) _v2 _v5)))))),
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
  _v2))))))))) := by
  exact @Body.round_path

-- Independent literal expected type for Body.seed_path.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0188 :
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
-- Complete literal proposition for Body.seed_path; original proof reused.
theorem PartACanonical.Surface.m0113 :
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
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@Body.clear _v0 _v1 _v2)))))))) := by
  exact @Body.seed_path

-- Independent literal expected type for Body.sweep.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0189 :
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
-- Complete literal proposition for Body.sweep; original proof reused.
theorem PartACanonical.Surface.m0114 :
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
  (@Nat) (@instAddNat)) _v1 _v2) _v0)))))) := by
  exact @Body.sweep

-- Independent literal expected type for Body.value.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0190 :
(∀ (_v0 : (@List.{0} (@Bool))),
(@Nat)))
end
-- Independent literal expected type for Body.value.eq_1.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0191 :
(@Eq.{(0 + 1)} (@Nat) (@Body.value (@List.nil.{0} (@Bool))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat)))))
end
-- Complete literal proposition for Body.value.eq_1; original proof reused.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Surface.m0115 :
(@Eq.{(0 + 1)} (@Nat) (@Body.value (@List.nil.{0} (@Bool))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat)))))
end
-- Independent literal expected type for Body.value.eq_2.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0192 :
(∀ (_v0 : (@Bool)),
(∀ (_v1 : (@List.{0} (@Bool))),
(@Eq.{(0 + 1)} (@Nat) (@Body.value (@List.cons.{0} (@Bool) _v0 _v1)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@Bool.toNat _v0) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@Body.value _v1)))))))
end
-- Complete literal proposition for Body.value.eq_2; original proof reused.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Surface.m0116 :
(∀ (_v0 : (@Bool)),
(∀ (_v1 : (@List.{0} (@Bool))),
(@Eq.{(0 + 1)} (@Nat) (@Body.value (@List.cons.{0} (@Bool) _v0 _v1)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@Bool.toNat _v0) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@Body.value _v1)))))))
end
-- Independent literal expected type for Body.value_lt.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0193 :
(∀ (_v0 : (@List.{0} (@Bool))),
(@LT.lt.{0} (@Nat) (@instLTNat) (@Body.value _v0) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat)
  (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  (@List.length.{0} (@Bool) _v0)))))
end
-- Complete literal proposition for Body.value_lt; original proof reused.
theorem PartACanonical.Surface.m0117 :
(∀ (_v0 : (@List.{0} (@Bool))),
(@LT.lt.{0} (@Nat) (@instLTNat) (@Body.value _v0) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat)
  (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  (@List.length.{0} (@Bool) _v0)))) := by
  exact @Body.value_lt

-- Independent literal expected type for Body.zero_value.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0194 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@Body.value (@List.replicate.{0} (@Bool) _v0 (@Bool.false))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))))))
end
-- Complete literal proposition for Body.zero_value; original proof reused.
theorem PartACanonical.Surface.m0118 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@Body.value (@List.replicate.{0} (@Bool) _v0 (@Bool.false))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))))) := by
  exact @Body.zero_value

-- Independent literal expected type for BodyIngress.Target.Body.
noncomputable def PartACanonical.Types.p0195 :
(∀ (_v0 : (@Nat)),
(Sort 0)) := by
  exact @BodyIngress.Target.Body

-- Independent literal expected type for BodyIngress.Target.Raw.
noncomputable def PartACanonical.Types.p0196 :
(∀ (_v0 : (@Nat)),
(Sort 0)) := by
  exact @BodyIngress.Target.Raw

-- Independent literal expected type for BodyIngress.accepted_frontier.
noncomputable def PartACanonical.Types.p0197 :
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
(let _v22 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11) := (@Pnp3.Complexity.Uniform.V1.initialConfig
  (@BodyIngress.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11
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
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@BodyIngress.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v28 _v22)
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@BodyIngress.old _v0 (@CarryWindow.embed _v0
  (@CanonicalLeaf.entry _v0))) _v24 (fun (_v29 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11))) =>
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
  (@BodyIngress.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@BodyIngress.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v28 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) _v22)
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@BodyIngress.old _v0 (@CarryWindow.embed _v0
  (@CanonicalLeaf.result _v0 (@Bool.false)))) _v24 (@Function.update.{(0 + 1), (0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11)) (fun (_v29
  : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11))) =>
(@Option.{0} (@Bool))) (@instDecidableEqFin (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11)) (fun (_v29 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11))) =>
(@_v25 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  _v11) _v29))) _v24 (@Option.some.{0} (@Bool) (@Bool.false))))) (@And (∀ (_v29 : (@Nat)),
(∀ (_v30 : (@LE.le.{0} (@Nat) (@instLENat) _v29 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v28 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@BodyIngress.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v29 _v22))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@BodyIngress.machine _v0))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@BodyIngress.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v29 _v22))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@BodyIngress.machine _v0)))))) (∀ (_v29 : (@Nat)),
(∀ (_v30 : (@LT.lt.{0} (@Nat) (@instLTNat) _v29 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v28 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))),
(∀ (_v31 : (@Bool)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@BodyIngress.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v29 _v22))
  (@BodyIngress.old _v0 (@CarryWindow.embed _v0 (@CanonicalLeaf.result _v0 _v31))))))))))))))))))))))))));
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
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@BodyIngress.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v28 _v22)
  (@BodyIngress.config _v0 _v10 _v11 (@CarryWindow.config _v0 _v10 _v11 (@VirtualLeaf.config _v0 _v10 _v11
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
(@BodyIngress.accepted_frontier._proof_1 _v0 _v1 _v2 _v6 _v7 _v30))) _v27)) (fun (_v30 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11))) =>
(@CappedWeight.Target.image _v21 _v13 _v12 _v14 _v16 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v12 _v0) _v0) (@Cursor.Target.W
  _v0 _v12) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11) _v30))))))))) (@And (∀ (_v30 :
  (@Nat)),
(∀ (_v31 : (@LT.lt.{0} (@Nat) (@instLTNat) _v30 _v28)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@BodyIngress.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v30 _v22))
  (@BodyIngress.old _v0 (@CarryWindow.embed _v0 (@VirtualLeaf.embed _v0 (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight
  (@IngressRepair.producer) (@Cursor.machine _v0) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (430 : Nat) (@instOfNatNat (430 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (93 : Nat) (@instOfNatNat (93 : Nat)))
  _v0)))))))))) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@BodyIngress.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@BodyIngress.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v28 _v29) _v22) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@BodyIngress.old _v0 (@CarryWindow.ready _v0))
  (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11)
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
(@BodyIngress.accepted_frontier._proof_2 _v0 _v1 _v2 _v6 _v7 _v30))) _v27)) (fun (_v30 : (@Fin
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
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@BodyIngress.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v30 _v22))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@BodyIngress.machine _v0))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@BodyIngress.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v30 _v22))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@BodyIngress.machine _v0)))))) (∀ (_v30 : (@Nat)),
(∀ (_v31 : (@LT.lt.{0} (@Nat) (@instLTNat) _v30 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v28 _v29))),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@BodyIngress.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v30 _v22))
  (@BodyIngress.old _v0 (@CarryWindow.ready _v0))))))))))))))))) (@Exists.{(0 + 1)} (@Nat) (fun (_v28 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v29 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v30 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v31 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v32 : (@Nat)) =>
(@And (@CappedWeight.Target.Cap _v0 _v12 _v16 _v28 _v29 _v30 _v31 _v32) (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v9
  (@Cursor.Target.M _v0 _v12 _v7)) (@_v25 (@Cursor.Target.image _v18 _v0 _v9 _v12 _v7
  _v14)))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @BodyIngress.accepted_frontier

-- Complete literal proposition for BodyIngress.accepted_frontier; original proof reused.
theorem PartACanonical.Surface.m0119 :
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
(let _v22 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11) := (@Pnp3.Complexity.Uniform.V1.initialConfig
  (@BodyIngress.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11
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
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@BodyIngress.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v28 _v22)
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@BodyIngress.old _v0 (@CarryWindow.embed _v0
  (@CanonicalLeaf.entry _v0))) _v24 (fun (_v29 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11))) =>
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
  (@BodyIngress.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@BodyIngress.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v28 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) _v22)
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@BodyIngress.old _v0 (@CarryWindow.embed _v0
  (@CanonicalLeaf.result _v0 (@Bool.false)))) _v24 (@Function.update.{(0 + 1), (0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11)) (fun (_v29
  : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11))) =>
(@Option.{0} (@Bool))) (@instDecidableEqFin (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11)) (fun (_v29 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11))) =>
(@_v25 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  _v11) _v29))) _v24 (@Option.some.{0} (@Bool) (@Bool.false))))) (@And (∀ (_v29 : (@Nat)),
(∀ (_v30 : (@LE.le.{0} (@Nat) (@instLENat) _v29 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v28 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@BodyIngress.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v29 _v22))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@BodyIngress.machine _v0))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@BodyIngress.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v29 _v22))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@BodyIngress.machine _v0)))))) (∀ (_v29 : (@Nat)),
(∀ (_v30 : (@LT.lt.{0} (@Nat) (@instLTNat) _v29 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v28 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))),
(∀ (_v31 : (@Bool)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@BodyIngress.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v29 _v22))
  (@BodyIngress.old _v0 (@CarryWindow.embed _v0 (@CanonicalLeaf.result _v0 _v31))))))))))))))))))))))))));
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
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@BodyIngress.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v28 _v22)
  (@BodyIngress.config _v0 _v10 _v11 (@CarryWindow.config _v0 _v10 _v11 (@VirtualLeaf.config _v0 _v10 _v11
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
(@BodyIngress.accepted_frontier._proof_1 _v0 _v1 _v2 _v6 _v7 _v30))) _v27)) (fun (_v30 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11))) =>
(@CappedWeight.Target.image _v21 _v13 _v12 _v14 _v16 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v12 _v0) _v0) (@Cursor.Target.W
  _v0 _v12) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11) _v30))))))))) (@And (∀ (_v30 :
  (@Nat)),
(∀ (_v31 : (@LT.lt.{0} (@Nat) (@instLTNat) _v30 _v28)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@BodyIngress.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v30 _v22))
  (@BodyIngress.old _v0 (@CarryWindow.embed _v0 (@VirtualLeaf.embed _v0 (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight
  (@IngressRepair.producer) (@Cursor.machine _v0) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (430 : Nat) (@instOfNatNat (430 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (93 : Nat) (@instOfNatNat (93 : Nat)))
  _v0)))))))))) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@BodyIngress.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@BodyIngress.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v28 _v29) _v22) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@BodyIngress.old _v0 (@CarryWindow.ready _v0))
  (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11)
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
(@BodyIngress.accepted_frontier._proof_2 _v0 _v1 _v2 _v6 _v7 _v30))) _v27)) (fun (_v30 : (@Fin
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
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@BodyIngress.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v30 _v22))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@BodyIngress.machine _v0))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@BodyIngress.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v30 _v22))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@BodyIngress.machine _v0)))))) (∀ (_v30 : (@Nat)),
(∀ (_v31 : (@LT.lt.{0} (@Nat) (@instLTNat) _v30 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v28 _v29))),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@BodyIngress.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v30 _v22))
  (@BodyIngress.old _v0 (@CarryWindow.ready _v0))))))))))))))))) (@Exists.{(0 + 1)} (@Nat) (fun (_v28 : (@Nat)) =>
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
  exact @BodyIngress.accepted_frontier

-- Independent literal expected type for BodyIngress.bodyConfig.
noncomputable def PartACanonical.Types.p0199 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@SerializedBody.machine)) _v1 _v2)),
(@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)) _v1
  _v2))))) := by
  exact @BodyIngress.bodyConfig

-- Independent literal expected type for BodyIngress.check_accepted_frontier.
noncomputable def PartACanonical.Types.p0201 :
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
(let _v22 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11) := (@Pnp3.Complexity.Uniform.V1.initialConfig
  (@BodyIngress.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11
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
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@BodyIngress.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v28 _v22)
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@BodyIngress.old _v0 (@CarryWindow.embed _v0
  (@CanonicalLeaf.entry _v0))) _v24 (fun (_v29 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11))) =>
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
  (@BodyIngress.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@BodyIngress.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v28 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) _v22)
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@BodyIngress.old _v0 (@CarryWindow.embed _v0
  (@CanonicalLeaf.result _v0 (@Bool.false)))) _v24 (@Function.update.{(0 + 1), (0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11)) (fun (_v29
  : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11))) =>
(@Option.{0} (@Bool))) (@instDecidableEqFin (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11)) (fun (_v29 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11))) =>
(@_v25 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  _v11) _v29))) _v24 (@Option.some.{0} (@Bool) (@Bool.false))))) (@And (∀ (_v29 : (@Nat)),
(∀ (_v30 : (@LE.le.{0} (@Nat) (@instLENat) _v29 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v28 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@BodyIngress.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v29 _v22))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@BodyIngress.machine _v0))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@BodyIngress.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v29 _v22))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@BodyIngress.machine _v0)))))) (∀ (_v29 : (@Nat)),
(∀ (_v30 : (@LT.lt.{0} (@Nat) (@instLTNat) _v29 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v28 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))),
(∀ (_v31 : (@Bool)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@BodyIngress.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v29 _v22))
  (@BodyIngress.old _v0 (@CarryWindow.embed _v0 (@CanonicalLeaf.result _v0 _v31))))))))))))))))))))))))));
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
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@BodyIngress.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v28 _v22)
  (@BodyIngress.config _v0 _v10 _v11 (@CarryWindow.config _v0 _v10 _v11 (@VirtualLeaf.config _v0 _v10 _v11
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
(@BodyIngress.accepted_frontier._proof_1 _v0 _v1 _v2 _v6 _v7 _v30))) _v27)) (fun (_v30 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11))) =>
(@CappedWeight.Target.image _v21 _v13 _v12 _v14 _v16 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v12 _v0) _v0) (@Cursor.Target.W
  _v0 _v12) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11) _v30))))))))) (@And (∀ (_v30 :
  (@Nat)),
(∀ (_v31 : (@LT.lt.{0} (@Nat) (@instLTNat) _v30 _v28)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@BodyIngress.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v30 _v22))
  (@BodyIngress.old _v0 (@CarryWindow.embed _v0 (@VirtualLeaf.embed _v0 (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight
  (@IngressRepair.producer) (@Cursor.machine _v0) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (430 : Nat) (@instOfNatNat (430 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (93 : Nat) (@instOfNatNat (93 : Nat)))
  _v0)))))))))) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@BodyIngress.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@BodyIngress.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v28 _v29) _v22) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@BodyIngress.old _v0 (@CarryWindow.ready _v0))
  (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11)
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
(@BodyIngress.accepted_frontier._proof_2 _v0 _v1 _v2 _v6 _v7 _v30))) _v27)) (fun (_v30 : (@Fin
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
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@BodyIngress.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v30 _v22))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@BodyIngress.machine _v0))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@BodyIngress.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v30 _v22))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@BodyIngress.machine _v0)))))) (∀ (_v30 : (@Nat)),
(∀ (_v31 : (@LT.lt.{0} (@Nat) (@instLTNat) _v30 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v28 _v29))),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@BodyIngress.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v30 _v22))
  (@BodyIngress.old _v0 (@CarryWindow.ready _v0))))))))))))))))) (@Exists.{(0 + 1)} (@Nat) (fun (_v28 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v29 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v30 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v31 : (@Nat)) =>
(@Exists.{(0 + 1)} (@Nat) (fun (_v32 : (@Nat)) =>
(@And (@CappedWeight.Target.Cap _v0 _v12 _v16 _v28 _v29 _v30 _v31 _v32) (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v9
  (@Cursor.Target.M _v0 _v12 _v7)) (@_v25 (@Cursor.Target.image _v18 _v0 _v9 _v12 _v7
  _v14)))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @BodyIngress.check_accepted_frontier

-- Complete literal proposition for BodyIngress.check_accepted_frontier; original proof reused.
theorem PartACanonical.Surface.m0121 :
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
(let _v22 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11) := (@Pnp3.Complexity.Uniform.V1.initialConfig
  (@BodyIngress.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11
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
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@BodyIngress.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v28 _v22)
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@BodyIngress.old _v0 (@CarryWindow.embed _v0
  (@CanonicalLeaf.entry _v0))) _v24 (fun (_v29 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11))) =>
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
  (@BodyIngress.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@BodyIngress.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v28 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) _v22)
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@BodyIngress.old _v0 (@CarryWindow.embed _v0
  (@CanonicalLeaf.result _v0 (@Bool.false)))) _v24 (@Function.update.{(0 + 1), (0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11)) (fun (_v29
  : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11))) =>
(@Option.{0} (@Bool))) (@instDecidableEqFin (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11)) (fun (_v29 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11))) =>
(@_v25 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  _v11) _v29))) _v24 (@Option.some.{0} (@Bool) (@Bool.false))))) (@And (∀ (_v29 : (@Nat)),
(∀ (_v30 : (@LE.le.{0} (@Nat) (@instLENat) _v29 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v28 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@BodyIngress.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v29 _v22))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@BodyIngress.machine _v0))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@BodyIngress.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v29 _v22))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@BodyIngress.machine _v0)))))) (∀ (_v29 : (@Nat)),
(∀ (_v30 : (@LT.lt.{0} (@Nat) (@instLTNat) _v29 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v28 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))),
(∀ (_v31 : (@Bool)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@BodyIngress.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v29 _v22))
  (@BodyIngress.old _v0 (@CarryWindow.embed _v0 (@CanonicalLeaf.result _v0 _v31))))))))))))))))))))))))));
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
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@BodyIngress.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v28 _v22)
  (@BodyIngress.config _v0 _v10 _v11 (@CarryWindow.config _v0 _v10 _v11 (@VirtualLeaf.config _v0 _v10 _v11
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
(@BodyIngress.accepted_frontier._proof_1 _v0 _v1 _v2 _v6 _v7 _v30))) _v27)) (fun (_v30 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11))) =>
(@CappedWeight.Target.image _v21 _v13 _v12 _v14 _v16 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v12 _v0) _v0) (@Cursor.Target.W
  _v0 _v12) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11) _v30))))))))) (@And (∀ (_v30 :
  (@Nat)),
(∀ (_v31 : (@LT.lt.{0} (@Nat) (@instLTNat) _v30 _v28)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@BodyIngress.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v30 _v22))
  (@BodyIngress.old _v0 (@CarryWindow.embed _v0 (@VirtualLeaf.embed _v0 (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight
  (@IngressRepair.producer) (@Cursor.machine _v0) (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (430 : Nat) (@instOfNatNat (430 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (93 : Nat) (@instOfNatNat (93 : Nat)))
  _v0)))))))))) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@BodyIngress.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@BodyIngress.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v28 _v29) _v22) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@BodyIngress.old _v0 (@CarryWindow.ready _v0))
  (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11)
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
(@BodyIngress.accepted_frontier._proof_2 _v0 _v1 _v2 _v6 _v7 _v30))) _v27)) (fun (_v30 : (@Fin
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
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@BodyIngress.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v30 _v22))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@BodyIngress.machine _v0))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@BodyIngress.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v30 _v22))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@BodyIngress.machine _v0)))))) (∀ (_v30 : (@Nat)),
(∀ (_v31 : (@LT.lt.{0} (@Nat) (@instLTNat) _v30 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v28 _v29))),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@BodyIngress.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v30 _v22))
  (@BodyIngress.old _v0 (@CarryWindow.ready _v0))))))))))))))))) (@Exists.{(0 + 1)} (@Nat) (fun (_v28 : (@Nat)) =>
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
  exact @BodyIngress.check_accepted_frontier

-- Independent literal expected type for BodyIngress.check_clock_slack.
noncomputable def PartACanonical.Types.p0203 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v2 _v3) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@HMul.hMul.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (8589934592 : Nat)
  (@instOfNatNat (8589934592 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))))),
(∀ (_v6 : (@LE.le.{0} (@Nat) (@instLENat) _v4 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (1073741824 : Nat) (@instOfNatNat (1073741824 : Nat))) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))))),
(@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v3) _v4) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (17179869184 : Nat) (@instOfNatNat (17179869184 : Nat))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat))))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 :
  Nat))))))))))))) := by
  exact @BodyIngress.check_clock_slack

-- Complete literal proposition for BodyIngress.check_clock_slack; original proof reused.
theorem PartACanonical.Surface.m0123 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v2 _v3) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@HMul.hMul.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (8589934592 : Nat)
  (@instOfNatNat (8589934592 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))))),
(∀ (_v6 : (@LE.le.{0} (@Nat) (@instLENat) _v4 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (1073741824 : Nat) (@instOfNatNat (1073741824 : Nat))) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))))),
(@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v3) _v4) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (17179869184 : Nat) (@instOfNatNat (17179869184 : Nat))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat))))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 :
  Nat))))))))))))) := by
  exact @BodyIngress.check_clock_slack

-- Independent literal expected type for BodyIngress.check_missing_payload.
noncomputable def PartACanonical.Types.p0205 :
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
  Nat)))))) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@BodyIngress.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v10 (@Pnp3.Complexity.Uniform.V1.initialConfig (@BodyIngress.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@BodyIngress.machine _v0))) (@Eq.{(0 + 1)} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v1 _v2 _v3 _v4)
  (@Bool.false)))))))))))))))) := by
  exact @BodyIngress.check_missing_payload

-- Complete literal proposition for BodyIngress.check_missing_payload; original proof reused.
theorem PartACanonical.Surface.m0125 :
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
  Nat)))))) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@BodyIngress.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v10 (@Pnp3.Complexity.Uniform.V1.initialConfig (@BodyIngress.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@BodyIngress.machine _v0))) (@Eq.{(0 + 1)} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v1 _v2 _v3 _v4)
  (@Bool.false)))))))))))))))) := by
  exact @BodyIngress.check_missing_payload

-- Independent literal expected type for BodyIngress.check_repair138.
noncomputable def PartACanonical.Types.p0206 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step
  (@BodyIngress.machine _v0) (@BodyIngress.old _v0 (@CarryWindow.embed _v0 (@VirtualLeaf.embed _v0
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqLeft (@IngressRepair.producer) (@Cursor.machine _v0) (@SmallIngress.q
  (@OfNat.ofNat.{0} (@Nat) (138 : Nat) (@instOfNatNat (138 : Nat)))))))) (@Option.none.{0} (@Bool))) (@Prod.mk.{0, 0}
  (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@BodyIngress.machine _v0))
  (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.none.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move.stay))))) := by
  exact @BodyIngress.check_repair138

-- Complete literal proposition for BodyIngress.check_repair138; original proof reused.
theorem PartACanonical.Surface.m0126 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step
  (@BodyIngress.machine _v0) (@BodyIngress.old _v0 (@CarryWindow.embed _v0 (@VirtualLeaf.embed _v0
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqLeft (@IngressRepair.producer) (@Cursor.machine _v0) (@SmallIngress.q
  (@OfNat.ofNat.{0} (@Nat) (138 : Nat) (@instOfNatNat (138 : Nat)))))))) (@Option.none.{0} (@Bool))) (@Prod.mk.{0, 0}
  (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@BodyIngress.machine _v0))
  (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.none.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move.stay))))) := by
  exact @BodyIngress.check_repair138

-- Independent literal expected type for BodyIngress.check_stall_reject.
noncomputable def PartACanonical.Types.p0207 :
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
  (2 : Nat)))))) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@BodyIngress.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) _v3 (@Pnp3.Complexity.Uniform.V1.initialConfig (@BodyIngress.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat
  (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v1 _v2))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@BodyIngress.machine _v0))) (@Eq.{(0 + 1)} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v1 _v2) (@Bool.false))))))))) := by
  exact @BodyIngress.check_stall_reject

-- Complete literal proposition for BodyIngress.check_stall_reject; original proof reused.
theorem PartACanonical.Surface.m0127 :
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
  (2 : Nat)))))) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@BodyIngress.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) _v3 (@Pnp3.Complexity.Uniform.V1.initialConfig (@BodyIngress.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat
  (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v1 _v2))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@BodyIngress.machine _v0))) (@Eq.{(0 + 1)} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v1 _v2) (@Bool.false))))))))) := by
  exact @BodyIngress.check_stall_reject

-- Independent literal expected type for BodyIngress.check_transport.
noncomputable def PartACanonical.Types.p0209 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ {_v3 : (@Nat)},
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine
  _v0)) _v1 _v2)),
(∀ (_v5 : (∀ (_v5 : (@Nat)),
(∀ (_v6 : (@LT.lt.{0} (@Nat) (@instLTNat) _v5 _v3)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))
  _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CarryWindow.machine _v0) _v1 _v2 _v5 _v4)) (@CarryWindow.ready
  _v0))))),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@LE.le.{0} (@Nat) (@instLENat) _v6 _v3)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@BodyIngress.machine _v0)) _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@BodyIngress.machine _v0) _v1 _v2 _v6
  (@BodyIngress.config _v0 _v1 _v2 _v4)) (@BodyIngress.config _v0 _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@CarryWindow.machine _v0) _v1 _v2 _v6 _v4))))))))))) := by
  exact @BodyIngress.check_transport

-- Complete literal proposition for BodyIngress.check_transport; original proof reused.
theorem PartACanonical.Surface.m0129 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ {_v3 : (@Nat)},
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine
  _v0)) _v1 _v2)),
(∀ (_v5 : (∀ (_v5 : (@Nat)),
(∀ (_v6 : (@LT.lt.{0} (@Nat) (@instLTNat) _v5 _v3)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))
  _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CarryWindow.machine _v0) _v1 _v2 _v5 _v4)) (@CarryWindow.ready
  _v0))))),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@LE.le.{0} (@Nat) (@instLENat) _v6 _v3)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@BodyIngress.machine _v0)) _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@BodyIngress.machine _v0) _v1 _v2 _v6
  (@BodyIngress.config _v0 _v1 _v2 _v4)) (@BodyIngress.config _v0 _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@CarryWindow.machine _v0) _v1 _v2 _v6 _v4))))))))))) := by
  exact @BodyIngress.check_transport

-- Independent literal expected type for BodyIngress.check_transport_stopped.
noncomputable def PartACanonical.Types.p0210 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ {_v3 : (@Nat)},
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine
  _v0)) _v1 _v2)),
(∀ (_v5 : (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))
  _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CarryWindow.machine _v0) _v1 _v2 _v3 _v4)) (@CarryWindow.ready
  _v0))),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@LE.le.{0} (@Nat) (@instLENat) _v6 _v3)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@BodyIngress.machine _v0)) _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@BodyIngress.machine _v0) _v1 _v2 _v6
  (@BodyIngress.config _v0 _v1 _v2 _v4)) (@BodyIngress.config _v0 _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@CarryWindow.machine _v0) _v1 _v2 _v6 _v4))))))))))) := by
  exact @BodyIngress.check_transport_stopped

-- Complete literal proposition for BodyIngress.check_transport_stopped; original proof reused.
theorem PartACanonical.Surface.m0130 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ {_v3 : (@Nat)},
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine
  _v0)) _v1 _v2)),
(∀ (_v5 : (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))
  _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CarryWindow.machine _v0) _v1 _v2 _v3 _v4)) (@CarryWindow.ready
  _v0))),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@LE.le.{0} (@Nat) (@instLENat) _v6 _v3)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@BodyIngress.machine _v0)) _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@BodyIngress.machine _v0) _v1 _v2 _v6
  (@BodyIngress.config _v0 _v1 _v2 _v4)) (@BodyIngress.config _v0 _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@CarryWindow.machine _v0) _v1 _v2 _v6 _v4))))))))))) := by
  exact @BodyIngress.check_transport_stopped

-- Independent literal expected type for BodyIngress.check_workspace_room.
noncomputable def PartACanonical.Types.p0211 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) _v0)),
(∀ (_v4 : (@LE.le.{0} (@Nat) (@instLENat) _v1 _v0)),
(∀ (_v5 : (@LE.le.{0} (@Nat) (@instLENat) _v2 _v0)),
(@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos
  _v0) _v1 _v2 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v0 (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation _v0))))))))) := by
  exact @BodyIngress.check_workspace_room

-- Complete literal proposition for BodyIngress.check_workspace_room; original proof reused.
theorem PartACanonical.Surface.m0131 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) _v0)),
(∀ (_v4 : (@LE.le.{0} (@Nat) (@instLENat) _v1 _v0)),
(∀ (_v5 : (@LE.le.{0} (@Nat) (@instLENat) _v2 _v0)),
(@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos
  _v0) _v1 _v2 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v0 (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation _v0))))))))) := by
  exact @BodyIngress.check_workspace_room

-- Independent literal expected type for BodyIngress.clock_slack.
noncomputable def PartACanonical.Types.p0212 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v2 _v3) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@HMul.hMul.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (8589934592 : Nat)
  (@instOfNatNat (8589934592 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))))),
(∀ (_v6 : (@LE.le.{0} (@Nat) (@instLENat) _v4 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (1073741824 : Nat) (@instOfNatNat (1073741824 : Nat))) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))))),
(@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v3) _v4) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (17179869184 : Nat) (@instOfNatNat (17179869184 : Nat))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat))))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 :
  Nat))))))))))))) := by
  exact @BodyIngress.clock_slack

-- Complete literal proposition for BodyIngress.clock_slack; original proof reused.
theorem PartACanonical.Surface.m0132 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v2 _v3) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@HMul.hMul.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (8589934592 : Nat)
  (@instOfNatNat (8589934592 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))))),
(∀ (_v6 : (@LE.le.{0} (@Nat) (@instLENat) _v4 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (1073741824 : Nat) (@instOfNatNat (1073741824 : Nat))) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))))),
(@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v3) _v4) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (17179869184 : Nat) (@instOfNatNat (17179869184 : Nat))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat))))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 :
  Nat))))))))))))) := by
  exact @BodyIngress.clock_slack

-- Independent literal expected type for BodyIngress.config.
noncomputable def PartACanonical.Types.p0213 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine
  _v0)) _v1 _v2)),
(@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)) _v1
  _v2))))) := by
  exact @BodyIngress.config

-- Independent literal expected type for BodyIngress.machine.
noncomputable def PartACanonical.Types.p0216 :
(∀ (_v0 : (@Nat)),
(@Pnp3.Complexity.Uniform.V1.UniformTM)) := by
  exact @BodyIngress.machine

-- Independent literal expected type for BodyIngress.missing_payload.
noncomputable def PartACanonical.Types.p0217 :
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
  Nat)))))) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@BodyIngress.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v10 (@Pnp3.Complexity.Uniform.V1.initialConfig (@BodyIngress.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@BodyIngress.machine _v0))) (@Eq.{(0 + 1)} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v1 _v2 _v3 _v4)
  (@Bool.false)))))))))))))))) := by
  exact @BodyIngress.missing_payload

-- Complete literal proposition for BodyIngress.missing_payload; original proof reused.
theorem PartACanonical.Surface.m0134 :
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
  Nat)))))) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@BodyIngress.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v10 (@Pnp3.Complexity.Uniform.V1.initialConfig (@BodyIngress.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@BodyIngress.machine _v0))) (@Eq.{(0 + 1)} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v1 _v2 _v3 _v4)
  (@Bool.false)))))))))))))))) := by
  exact @BodyIngress.missing_payload

-- Independent literal expected type for BodyIngress.repair138.
noncomputable def PartACanonical.Types.p0219 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step
  (@BodyIngress.machine _v0) (@BodyIngress.old _v0 (@CarryWindow.embed _v0 (@VirtualLeaf.embed _v0
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqLeft (@IngressRepair.producer) (@Cursor.machine _v0) (@SmallIngress.q
  (@OfNat.ofNat.{0} (@Nat) (138 : Nat) (@instOfNatNat (138 : Nat)))))))) (@Option.none.{0} (@Bool))) (@Prod.mk.{0, 0}
  (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@BodyIngress.machine _v0))
  (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.none.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move.stay))))) := by
  exact @BodyIngress.repair138

-- Complete literal proposition for BodyIngress.repair138; original proof reused.
theorem PartACanonical.Surface.m0135 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step
  (@BodyIngress.machine _v0) (@BodyIngress.old _v0 (@CarryWindow.embed _v0 (@VirtualLeaf.embed _v0
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqLeft (@IngressRepair.producer) (@Cursor.machine _v0) (@SmallIngress.q
  (@OfNat.ofNat.{0} (@Nat) (138 : Nat) (@instOfNatNat (138 : Nat)))))))) (@Option.none.{0} (@Bool))) (@Prod.mk.{0, 0}
  (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@BodyIngress.machine _v0))
  (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.none.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move.stay))))) := by
  exact @BodyIngress.repair138

-- Independent literal expected type for BodyIngress.stall_reject.
noncomputable def PartACanonical.Types.p0220 :
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
  (2 : Nat)))))) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@BodyIngress.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) _v3 (@Pnp3.Complexity.Uniform.V1.initialConfig (@BodyIngress.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat
  (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v1 _v2))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@BodyIngress.machine _v0))) (@Eq.{(0 + 1)} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v1 _v2) (@Bool.false))))))))) := by
  exact @BodyIngress.stall_reject

-- Complete literal proposition for BodyIngress.stall_reject; original proof reused.
theorem PartACanonical.Surface.m0136 :
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
  (2 : Nat)))))) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@BodyIngress.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@BodyIngress.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) _v3 (@Pnp3.Complexity.Uniform.V1.initialConfig (@BodyIngress.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat
  (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v1 _v2))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@BodyIngress.machine _v0))) (@Eq.{(0 + 1)} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v1 _v2) (@Bool.false))))))))) := by
  exact @BodyIngress.stall_reject

-- Independent literal expected type for BodyIngress.transport.
noncomputable def PartACanonical.Types.p0222 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ {_v3 : (@Nat)},
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine
  _v0)) _v1 _v2)),
(∀ (_v5 : (∀ (_v5 : (@Nat)),
(∀ (_v6 : (@LT.lt.{0} (@Nat) (@instLTNat) _v5 _v3)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))
  _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CarryWindow.machine _v0) _v1 _v2 _v5 _v4)) (@CarryWindow.ready
  _v0))))),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@LE.le.{0} (@Nat) (@instLENat) _v6 _v3)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@BodyIngress.machine _v0)) _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@BodyIngress.machine _v0) _v1 _v2 _v6
  (@BodyIngress.config _v0 _v1 _v2 _v4)) (@BodyIngress.config _v0 _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@CarryWindow.machine _v0) _v1 _v2 _v6 _v4))))))))))) := by
  exact @BodyIngress.transport

-- Complete literal proposition for BodyIngress.transport; original proof reused.
theorem PartACanonical.Surface.m0138 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ {_v3 : (@Nat)},
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine
  _v0)) _v1 _v2)),
(∀ (_v5 : (∀ (_v5 : (@Nat)),
(∀ (_v6 : (@LT.lt.{0} (@Nat) (@instLTNat) _v5 _v3)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))
  _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CarryWindow.machine _v0) _v1 _v2 _v5 _v4)) (@CarryWindow.ready
  _v0))))),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@LE.le.{0} (@Nat) (@instLENat) _v6 _v3)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@BodyIngress.machine _v0)) _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@BodyIngress.machine _v0) _v1 _v2 _v6
  (@BodyIngress.config _v0 _v1 _v2 _v4)) (@BodyIngress.config _v0 _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@CarryWindow.machine _v0) _v1 _v2 _v6 _v4))))))))))) := by
  exact @BodyIngress.transport

-- Independent literal expected type for BodyIngress.transport_stopped.
noncomputable def PartACanonical.Types.p0223 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ {_v3 : (@Nat)},
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine
  _v0)) _v1 _v2)),
(∀ (_v5 : (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))
  _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CarryWindow.machine _v0) _v1 _v2 _v3 _v4)) (@CarryWindow.ready
  _v0))),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@LE.le.{0} (@Nat) (@instLENat) _v6 _v3)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@BodyIngress.machine _v0)) _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@BodyIngress.machine _v0) _v1 _v2 _v6
  (@BodyIngress.config _v0 _v1 _v2 _v4)) (@BodyIngress.config _v0 _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@CarryWindow.machine _v0) _v1 _v2 _v6 _v4))))))))))) := by
  exact @BodyIngress.transport_stopped

-- Complete literal proposition for BodyIngress.transport_stopped; original proof reused.
theorem PartACanonical.Surface.m0139 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ {_v3 : (@Nat)},
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine
  _v0)) _v1 _v2)),
(∀ (_v5 : (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CarryWindow.machine _v0))
  _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CarryWindow.machine _v0) _v1 _v2 _v3 _v4)) (@CarryWindow.ready
  _v0))),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@LE.le.{0} (@Nat) (@instLENat) _v6 _v3)),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@BodyIngress.machine _v0)) _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@BodyIngress.machine _v0) _v1 _v2 _v6
  (@BodyIngress.config _v0 _v1 _v2 _v4)) (@BodyIngress.config _v0 _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@CarryWindow.machine _v0) _v1 _v2 _v6 _v4))))))))))) := by
  exact @BodyIngress.transport_stopped

-- Independent literal expected type for BodyIngress.workspace_room.
noncomputable def PartACanonical.Types.p0224 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) _v0)),
(∀ (_v4 : (@LE.le.{0} (@Nat) (@instLENat) _v1 _v0)),
(∀ (_v5 : (@LE.le.{0} (@Nat) (@instLENat) _v2 _v0)),
(@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos
  _v0) _v1 _v2 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v0 (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation _v0))))))))) := by
  exact @BodyIngress.workspace_room

-- Complete literal proposition for BodyIngress.workspace_room; original proof reused.
theorem PartACanonical.Surface.m0140 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) _v0)),
(∀ (_v4 : (@LE.le.{0} (@Nat) (@instLENat) _v1 _v0)),
(∀ (_v5 : (@LE.le.{0} (@Nat) (@instLENat) _v2 _v0)),
(@LT.lt.{0} (@Nat) (@instLTNat) (@SerializedBody.delimiter (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos
  _v0) _v1 _v2 (@OfNat.ofNat.{0} (@Nat) (12 : Nat) (@instOfNatNat (12 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v0 (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation _v0))))))))) := by
  exact @BodyIngress.workspace_room

-- Independent literal expected type for CanonicalLeaf.Target.Body.
noncomputable def PartACanonical.Types.p0225 :
(∀ (_v0 : (@Nat)),
(Sort 0)) := by
  exact @CanonicalLeaf.Target.Body

-- Independent literal expected type for CanonicalLeaf.Target.Raw.
noncomputable def PartACanonical.Types.p0226 :
(∀ (_v0 : (@Nat)),
(Sort 0)) := by
  exact @CanonicalLeaf.Target.Raw

-- Independent literal expected type for CanonicalLeaf.accepted_leaf.
noncomputable def PartACanonical.Types.p0227 :
(∀ (_v0 : (@Nat)),
(@CanonicalLeaf.Target.Raw _v0)) := by
  exact @CanonicalLeaf.accepted_leaf

-- Complete literal proposition for CanonicalLeaf.accepted_leaf; original proof reused.
theorem PartACanonical.Surface.m0141 :
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
  (@CanonicalLeaf.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig (@CanonicalLeaf.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair
  _v1 _v2 _v3 _v4));
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
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@CanonicalLeaf.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v28 _v22)
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@CanonicalLeaf.entry _v0) _v24 (fun (_v29 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11))) =>
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
  (@CanonicalLeaf.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CanonicalLeaf.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v28 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) _v22)
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@CanonicalLeaf.result _v0 (@Bool.false)) _v24
  (@Function.update.{(0 + 1), (0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11)) (fun (_v29 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11))) =>
(@Option.{0} (@Bool))) (@instDecidableEqFin (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11)) (fun (_v29 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11))) =>
(@_v25 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  _v11) _v29))) _v24 (@Option.some.{0} (@Bool) (@Bool.false))))) (@And (∀ (_v29 : (@Nat)),
(∀ (_v30 : (@LE.le.{0} (@Nat) (@instLENat) _v29 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v28 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@CanonicalLeaf.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v29 _v22))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@CanonicalLeaf.machine _v0))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@CanonicalLeaf.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v29 _v22))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@CanonicalLeaf.machine _v0)))))) (∀ (_v29 : (@Nat)),
(∀ (_v30 : (@LT.lt.{0} (@Nat) (@instLTNat) _v29 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v28 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))),
(∀ (_v31 : (@Bool)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@CanonicalLeaf.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v29 _v22))
  (@CanonicalLeaf.result _v0 _v31))))))))))))))))))))))));
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
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (524288 : Nat)
  (@instOfNatNat (524288 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))))) (@And (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v28 _v29) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (4294967296 : Nat) (@instOfNatNat (4294967296 : Nat))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))) (@And (@Eq.{(0 + 1)}
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@CanonicalLeaf.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v28 _v22)
  (@VirtualLeaf.config _v0 _v10 _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@IngressRepair.producer)
  (@Cursor.machine _v0) _v10 _v11 (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Cursor.machine _v0)) _v10 _v11 (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (430 : Nat) (@instOfNatNat (430 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (93 : Nat) (@instOfNatNat (93 : Nat))) _v0)))
  (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 _v16) _v12) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (@CanonicalLeaf.Target.Raw._proof_3 _v0 _v1 _v2 _v6 _v7 _v27)) (fun (_v30 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11))) =>
(@CappedWeight.Target.image _v21 _v13 _v12 _v14 _v16 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) _v12 _v0) _v0) (@Cursor.Target.W
  _v0 _v12) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11) _v30))))))) (@And (∀ (_v30 :
  (@Nat)),
(∀ (_v31 : (@LT.lt.{0} (@Nat) (@instLTNat) _v30 _v28)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@CanonicalLeaf.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 _v30 _v22))
  (@VirtualLeaf.embed _v0 (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@IngressRepair.producer) (@Cursor.machine _v0)
  (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat)
  (430 : Nat) (@instOfNatNat (430 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (93 : Nat) (@instOfNatNat (93 : Nat))) _v0)))))))) (@Eq.{(0 + 1)}
  (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@CanonicalLeaf.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v11 (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v28 _v29) _v22) (@VirtualLeaf.config _v0 _v10 _v11
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@IngressRepair.producer) (@Cursor.machine _v0) _v10 _v11
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0)) _v10
  _v11 (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0}
  (@Nat) (613 : Nat) (@instOfNatNat (613 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (93 : Nat) (@instOfNatNat (93 : Nat))) _v0))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v14 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@CanonicalLeaf.Target.Raw._proof_4
  _v0 _v1 _v2 _v6 _v7 _v27)) (fun (_v30 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11))) =>
(@CappedWeight.Target.image _v21 _v13 _v12 _v14 _v16 (@Pnp4.Frontier.ContractExpansion.bitLength (@Cursor.Target.W _v0
  _v12)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat))) (@Cursor.Target.W _v0 _v12) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v10 _v11) _v30))))))))))))))))) (@Exists.{(0 + 1)} (@Nat) (fun (_v28 : (@Nat))
  =>
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
  exact @CanonicalLeaf.accepted_leaf

-- Independent literal expected type for CanonicalLeaf.controls.
noncomputable def PartACanonical.Types.p0228 :
(∀ (_v0 : (@Nat)),
(@And (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@VirtualLeaf.machine _v0))) (@And (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.start (@CanonicalLeaf.machine _v0)) (@Pnp3.Complexity.Uniform.V1.UniformTM.start
  (@VirtualLeaf.machine _v0))) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@CanonicalLeaf.machine _v0))) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@CanonicalLeaf.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@VirtualLeaf.machine _v0))) (@And (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@CanonicalLeaf.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@VirtualLeaf.machine _v0))) (@And (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0))) (@CanonicalLeaf.entry _v0)
  (@VirtualLeaf.embed _v0 (@VirtualLeaf.entry _v0))) (∀ (_v1 : (@Bool)),
(@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0)))
  (@CanonicalLeaf.result _v0 _v1) (@VirtualLeaf.result _v0 _v1))))))))) := by
  exact @CanonicalLeaf.controls

-- Complete literal proposition for CanonicalLeaf.controls; original proof reused.
theorem PartACanonical.Surface.m0142 :
(∀ (_v0 : (@Nat)),
(@And (@Eq.{(0 + 1)} (@Nat) (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@VirtualLeaf.machine _v0))) (@And (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.start (@CanonicalLeaf.machine _v0)) (@Pnp3.Complexity.Uniform.V1.UniformTM.start
  (@VirtualLeaf.machine _v0))) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@CanonicalLeaf.machine _v0))) (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@CanonicalLeaf.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@VirtualLeaf.machine _v0))) (@And (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@CanonicalLeaf.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@VirtualLeaf.machine _v0))) (@And (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0))) (@CanonicalLeaf.entry _v0)
  (@VirtualLeaf.embed _v0 (@VirtualLeaf.entry _v0))) (∀ (_v1 : (@Bool)),
(@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0)))
  (@CanonicalLeaf.result _v0 _v1) (@VirtualLeaf.result _v0 _v1))))))))) := by
  exact @CanonicalLeaf.controls

-- Independent literal expected type for CanonicalLeaf.counter_frame.
noncomputable def PartACanonical.Types.p0229 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Bool)),
(∀ (_v8 : (@LT.lt.{0} (@Nat) (@instLTNat) _v5 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v3))),
(∀ (_v9 : (@Fin _v3)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Stream.Target.image _v0 _v1 _v2 _v3 _v4 _v5 _v6 _v7 (@HSub.hSub.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v2) _v3) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Fin.val _v3 _v9))) (@Option.some.{0} (@Bool) (@Pnp3.Core.vecOfNat _v3 _v5
  _v9))))))))))))) := by
  exact @CanonicalLeaf.counter_frame

-- Complete literal proposition for CanonicalLeaf.counter_frame; original proof reused.
theorem PartACanonical.Surface.m0143 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Bool)),
(∀ (_v8 : (@LT.lt.{0} (@Nat) (@instLTNat) _v5 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v3))),
(∀ (_v9 : (@Fin _v3)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Stream.Target.image _v0 _v1 _v2 _v3 _v4 _v5 _v6 _v7 (@HSub.hSub.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v2) _v3) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Fin.val _v3 _v9))) (@Option.some.{0} (@Bool) (@Pnp3.Core.vecOfNat _v3 _v5
  _v9))))))))))))) := by
  exact @CanonicalLeaf.counter_frame

-- Independent literal expected type for CanonicalLeaf.counter_leaf.
noncomputable def PartACanonical.Types.p0230 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Nat)),
(∀ (_v8 : (@Nat)),
(∀ (_v9 : (@Bool)),
(∀ (_v10 : (∀ (_v10 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v11 : (@LT.lt.{0} (@Nat) (@instLTNat) _v7 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat)
  (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v5))),
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) _v5) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))),
(∀ (_v13 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Stream.Target.image _v10 _v3 _v4 _v5 _v6 _v7 _v8 _v9 (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))
  (@Option.none.{0} (@Bool)))),
(∀ (_v14 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Stream.Target.image _v10 _v3 _v4 _v5 _v6 _v7 _v8 _v9 (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3
  _v4) _v5) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))) (@Option.none.{0} (@Bool)))),
(let _v15 : (∀ (_v15 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))),
(@Option.{0} (@Bool))) := (fun (_v15 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))) =>
(@Stream.Target.image _v10 _v3 _v4 _v5 _v6 _v7 _v8 _v9 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)
  _v15)));
(let _v16 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) := (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v1 _v2) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 _v4) _v5) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v12);
(let _v17 : (@Bool) := (@ite.{(0 + 1)} (@Bool) (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) _v5) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v5)
  (@Nat.testBit _v7 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Bool.false));
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@CanonicalLeaf.machine _v0)) _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CanonicalLeaf.machine _v0) _v1 _v2
  (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0)) _v1 _v2 (@CanonicalLeaf.entry _v0) _v16
  _v15)) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine
  _v0)) _v1 _v2 (@ite.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0)))
  (@Eq.{(0 + 1)} (@Nat) _v5 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat _v5
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject
  (@CanonicalLeaf.machine _v0)) (@CanonicalLeaf.result _v0 _v17)) _v16 (@ite.{(0 + 1)} (∀ (_v18 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))),
(@Option.{0} (@Bool))) (@Eq.{(0 + 1)} (@Nat) _v5 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@instDecidableEqNat _v5 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v15 (@Function.update.{(0 + 1),
  (0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (fun (_v18 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))) =>
(@Option.{0} (@Bool))) (@instDecidableEqFin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) _v15 _v16
  (@Option.some.{0} (@Bool) _v17))))))))))))))))))))))) := by
  exact @CanonicalLeaf.counter_leaf

-- Complete literal proposition for CanonicalLeaf.counter_leaf; original proof reused.
theorem PartACanonical.Surface.m0144 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Nat)),
(∀ (_v8 : (@Nat)),
(∀ (_v9 : (@Bool)),
(∀ (_v10 : (∀ (_v10 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v11 : (@LT.lt.{0} (@Nat) (@instLTNat) _v7 (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat)
  (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v5))),
(∀ (_v12 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) _v5) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))),
(∀ (_v13 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Stream.Target.image _v10 _v3 _v4 _v5 _v6 _v7 _v8 _v9 (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))
  (@Option.none.{0} (@Bool)))),
(∀ (_v14 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Stream.Target.image _v10 _v3 _v4 _v5 _v6 _v7 _v8 _v9 (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3
  _v4) _v5) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))) (@Option.none.{0} (@Bool)))),
(let _v15 : (∀ (_v15 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))),
(@Option.{0} (@Bool))) := (fun (_v15 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))) =>
(@Stream.Target.image _v10 _v3 _v4 _v5 _v6 _v7 _v8 _v9 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)
  _v15)));
(let _v16 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) := (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v1 _v2) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 _v4) _v5) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v12);
(let _v17 : (@Bool) := (@ite.{(0 + 1)} (@Bool) (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) _v5) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v5)
  (@Nat.testBit _v7 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Bool.false));
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@CanonicalLeaf.machine _v0)) _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CanonicalLeaf.machine _v0) _v1 _v2
  (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0)) _v1 _v2 (@CanonicalLeaf.entry _v0) _v16
  _v15)) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine
  _v0)) _v1 _v2 (@ite.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0)))
  (@Eq.{(0 + 1)} (@Nat) _v5 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat _v5
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject
  (@CanonicalLeaf.machine _v0)) (@CanonicalLeaf.result _v0 _v17)) _v16 (@ite.{(0 + 1)} (∀ (_v18 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))),
(@Option.{0} (@Bool))) (@Eq.{(0 + 1)} (@Nat) _v5 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@instDecidableEqNat _v5 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v15 (@Function.update.{(0 + 1),
  (0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (fun (_v18 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))) =>
(@Option.{0} (@Bool))) (@instDecidableEqFin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) _v15 _v16
  (@Option.some.{0} (@Bool) _v17))))))))))))))))))))))) := by
  exact @CanonicalLeaf.counter_leaf

-- Independent literal expected type for CanonicalLeaf.discriminator.
noncomputable def PartACanonical.Types.p0231 :
(∀ (_v0 : (@Nat)),
(let _v1 : (∀ (_v1 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0
  : Nat))) (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat)))))),
(@Option.{0} (@Bool))) := (fun (_v1 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat)))))) =>
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Or (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 :
  Nat)))) _v1) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Eq.{(0 + 1)} (@Nat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0}
  (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat)))) _v1) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))))
  (@instDecidableOr (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength (@OfNat.ofNat.{0} (@Nat) (0 :
  Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat)))) _v1) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 :
  Nat)))) _v1) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@instDecidableEqNat (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0}
  (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat)))) _v1) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@instDecidableEqNat (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat)))) _v1) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))))) (@Option.none.{0} (@Bool)) (@Option.some.{0} (@Bool) (@BEq.beq.{0} (@Nat)
  (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 :
  Nat)))) _v1) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))));
(let _v2 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat))))) := (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) (@of_decide_eq_true (@LT.lt.{0} (@Nat)
  (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 :
  Nat))))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0}
  (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat))))) (@id.{0} (@Eq.{(0 + 1)} (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat)
  (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 :
  Nat))))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0}
  (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat)))))) (@Bool.true)) (@Eq.refl.{(0 + 1)} (@Bool) (@Bool.true)))));
(let _v3 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine
  _v0)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat
  (16 : Nat)))) := (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@CanonicalLeaf.machine _v0)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (16
  : Nat) (@instOfNatNat (16 : Nat))) (@CanonicalLeaf.entry _v0) _v2 _v1);
(@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@CanonicalLeaf.machine _v0)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (16
  : Nat) (@instOfNatNat (16 : Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CanonicalLeaf.machine _v0)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v3) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat))) (@CanonicalLeaf.result _v0
  (@Bool.true)) _v2 (@Function.update.{(0 + 1), (0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat))))) (fun (_v4
  : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat)))))) =>
(@Option.{0} (@Bool))) (@instDecidableEqFin (@Pnp3.Complexity.Uniform.V1.tapeLength (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat))))) _v1 _v2 (@Option.some.{0}
  (@Bool) (@Bool.true))))) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@VirtualLeaf.machine _v0)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@VirtualLeaf.machine _v0) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat))) (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat))) _v3) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@VirtualLeaf.machine _v0)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (16 :
  Nat) (@instOfNatNat (16 : Nat))) (@VirtualLeaf.result _v0 (@Bool.false)) _v2 (@Function.update.{(0 + 1), (0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0}
  (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat))))) (fun (_v4 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 :
  Nat)))))) =>
(@Option.{0} (@Bool))) (@instDecidableEqFin (@Pnp3.Complexity.Uniform.V1.tapeLength (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat))))) _v1 _v2 (@Option.some.{0}
  (@Bool) (@Bool.false))))) (∀ (_v4 : (@Fin (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength (@OfNat.ofNat.{0} (@Nat) (0
  : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat)))) (@HSub.hSub.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0}
  (@Nat) (@instSubNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)) (@id.{0}
  (@LT.lt.{0} (@Nat) (@instLTNat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat))
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Fin.val (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)) (@Pnp3.Complexity.Uniform.V1.tapeLength (@OfNat.ofNat.{0} (@Nat) (0 :
  Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat)))))
  (@Decidable.byContradiction (@LT.lt.{0} (@Nat) (@instLTNat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0}
  (@Nat) (@instSubNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)) (@OfNat.ofNat.{0} (@Nat) (17 : Nat) (@instOfNatNat
  (17 : Nat)))) (@Nat.decLt (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat))
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Fin.val (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)) (@OfNat.ofNat.{0} (@Nat) (17 : Nat) (@instOfNatNat (17 : Nat)))) (fun
  (_v5 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@OfNat.ofNat.{0} (@Nat)
  (3 : Nat) (@instOfNatNat (3 : Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)) (@OfNat.ofNat.{0} (@Nat) (17 : Nat) (@instOfNatNat
  (17 : Nat)))))) =>
(@CanonicalLeaf.discriminator._proof_1 _v4 _v5)))))) (@Option.some.{0} (@Bool) (@Pnp3.Core.vecOfNat (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) _v4)))))))))) := by
  exact @CanonicalLeaf.discriminator

-- Complete literal proposition for CanonicalLeaf.discriminator; original proof reused.
theorem PartACanonical.Surface.m0145 :
(∀ (_v0 : (@Nat)),
(let _v1 : (∀ (_v1 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0
  : Nat))) (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat)))))),
(@Option.{0} (@Bool))) := (fun (_v1 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat)))))) =>
(@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Or (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 :
  Nat)))) _v1) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Eq.{(0 + 1)} (@Nat) (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0}
  (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat)))) _v1) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))))
  (@instDecidableOr (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength (@OfNat.ofNat.{0} (@Nat) (0 :
  Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat)))) _v1) (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Eq.{(0 + 1)} (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 :
  Nat)))) _v1) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@instDecidableEqNat (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0}
  (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat)))) _v1) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@instDecidableEqNat (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat)))) _v1) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))))) (@Option.none.{0} (@Bool)) (@Option.some.{0} (@Bool) (@BEq.beq.{0} (@Nat)
  (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 :
  Nat)))) _v1) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))));
(let _v2 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat))))) := (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) (@of_decide_eq_true (@LT.lt.{0} (@Nat)
  (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 :
  Nat))))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0}
  (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat))))) (@id.{0} (@Eq.{(0 + 1)} (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat)
  (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 :
  Nat))))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0}
  (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat)))))) (@Bool.true)) (@Eq.refl.{(0 + 1)} (@Bool) (@Bool.true)))));
(let _v3 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine
  _v0)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat
  (16 : Nat)))) := (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@CanonicalLeaf.machine _v0)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (16
  : Nat) (@instOfNatNat (16 : Nat))) (@CanonicalLeaf.entry _v0) _v2 _v1);
(@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@CanonicalLeaf.machine _v0)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (16
  : Nat) (@instOfNatNat (16 : Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CanonicalLeaf.machine _v0)
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v3) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat))) (@CanonicalLeaf.result _v0
  (@Bool.true)) _v2 (@Function.update.{(0 + 1), (0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat))))) (fun (_v4
  : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat)))))) =>
(@Option.{0} (@Bool))) (@instDecidableEqFin (@Pnp3.Complexity.Uniform.V1.tapeLength (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat))))) _v1 _v2 (@Option.some.{0}
  (@Bool) (@Bool.true))))) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@VirtualLeaf.machine _v0)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@VirtualLeaf.machine _v0) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat))) (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat))) _v3) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@VirtualLeaf.machine _v0)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (16 :
  Nat) (@instOfNatNat (16 : Nat))) (@VirtualLeaf.result _v0 (@Bool.false)) _v2 (@Function.update.{(0 + 1), (0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0}
  (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat))))) (fun (_v4 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 :
  Nat)))))) =>
(@Option.{0} (@Bool))) (@instDecidableEqFin (@Pnp3.Complexity.Uniform.V1.tapeLength (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat))))) _v1 _v2 (@Option.some.{0}
  (@Bool) (@Bool.false))))) (∀ (_v4 : (@Fin (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v1 (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength (@OfNat.ofNat.{0} (@Nat) (0
  : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat)))) (@HSub.hSub.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0}
  (@Nat) (@instSubNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)) (@id.{0}
  (@LT.lt.{0} (@Nat) (@instLTNat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat))
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Fin.val (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)) (@Pnp3.Complexity.Uniform.V1.tapeLength (@OfNat.ofNat.{0} (@Nat) (0 :
  Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (16 : Nat) (@instOfNatNat (16 : Nat)))))
  (@Decidable.byContradiction (@LT.lt.{0} (@Nat) (@instLTNat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0}
  (@Nat) (@instSubNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)) (@OfNat.ofNat.{0} (@Nat) (17 : Nat) (@instOfNatNat
  (17 : Nat)))) (@Nat.decLt (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat))
  (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Fin.val (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)) (@OfNat.ofNat.{0} (@Nat) (17 : Nat) (@instOfNatNat (17 : Nat)))) (fun
  (_v5 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@OfNat.ofNat.{0} (@Nat)
  (3 : Nat) (@instOfNatNat (3 : Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)) (@OfNat.ofNat.{0} (@Nat) (17 : Nat) (@instOfNatNat
  (17 : Nat)))))) =>
(@CanonicalLeaf.discriminator._proof_1 _v4 _v5)))))) (@Option.some.{0} (@Bool) (@Pnp3.Core.vecOfNat (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) _v4)))))))))) := by
  exact @CanonicalLeaf.discriminator

-- Independent literal expected type for CanonicalLeaf.entry.
noncomputable def PartACanonical.Types.p0232 :
(∀ (_v0 : (@Nat)),
(@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0)))) := by
  exact @CanonicalLeaf.entry

-- Independent literal expected type for CanonicalLeaf.machine.
noncomputable def PartACanonical.Types.p0233 :
(∀ (_v0 : (@Nat)),
(@Pnp3.Complexity.Uniform.V1.UniformTM)) := by
  exact @CanonicalLeaf.machine

-- Independent literal expected type for CanonicalLeaf.missing_payload.
noncomputable def PartACanonical.Types.p0234 :
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
  Nat)))))) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CanonicalLeaf.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v10 (@Pnp3.Complexity.Uniform.V1.initialConfig (@CanonicalLeaf.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@CanonicalLeaf.machine _v0))) (@Eq.{(0 + 1)} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v1 _v2 _v3 _v4)
  (@Bool.false)))))))))))))))) := by
  exact @CanonicalLeaf.missing_payload

-- Complete literal proposition for CanonicalLeaf.missing_payload; original proof reused.
theorem PartACanonical.Surface.m0146 :
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
  Nat)))))) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CanonicalLeaf.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) _v10 (@Pnp3.Complexity.Uniform.V1.initialConfig (@CanonicalLeaf.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1
  _v2)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair _v1 _v2 _v3 _v4))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@CanonicalLeaf.machine _v0))) (@Eq.{(0 + 1)} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v1 _v2 _v3 _v4)
  (@Bool.false)))))))))))))))) := by
  exact @CanonicalLeaf.missing_payload

-- Independent literal expected type for CanonicalLeaf.normal_work.
noncomputable def PartACanonical.Types.p0235 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine
  _v0)) _v1 _v2)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))),
(∀ (_v6 : (∀ (_v6 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))),
(@Option.{0} (@Bool)))),
(∀ (_v7 : (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@CanonicalLeaf.machine _v0)) _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CanonicalLeaf.machine _v0) _v1 _v2
  _v4 _v3) (@VirtualLeaf.config _v0 _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@IngressRepair.producer)
  (@Cursor.machine _v0) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Cursor.machine _v0)) _v1 _v2 (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (613 : Nat) (@instOfNatNat (613 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (93 : Nat) (@instOfNatNat (93 : Nat))) _v0))) _v5
  _v6))))),
(∀ (_v8 : (@Nat)),
(∀ (_v9 : (@LE.le.{0} (@Nat) (@instLENat) _v8 _v4)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine
  _v0)) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CanonicalLeaf.machine _v0) _v1 _v2 _v8 _v3))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@CanonicalLeaf.machine _v0))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine
  _v0)) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CanonicalLeaf.machine _v0) _v1 _v2 _v8 _v3))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@CanonicalLeaf.machine _v0)))))))))))))) := by
  exact @CanonicalLeaf.normal_work

-- Complete literal proposition for CanonicalLeaf.normal_work; original proof reused.
theorem PartACanonical.Surface.m0147 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine
  _v0)) _v1 _v2)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))),
(∀ (_v6 : (∀ (_v6 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))),
(@Option.{0} (@Bool)))),
(∀ (_v7 : (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@CanonicalLeaf.machine _v0)) _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CanonicalLeaf.machine _v0) _v1 _v2
  _v4 _v3) (@VirtualLeaf.config _v0 _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@IngressRepair.producer)
  (@Cursor.machine _v0) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Cursor.machine _v0)) _v1 _v2 (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (613 : Nat) (@instOfNatNat (613 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (93 : Nat) (@instOfNatNat (93 : Nat))) _v0))) _v5
  _v6))))),
(∀ (_v8 : (@Nat)),
(∀ (_v9 : (@LE.le.{0} (@Nat) (@instLENat) _v8 _v4)),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine
  _v0)) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CanonicalLeaf.machine _v0) _v1 _v2 _v8 _v3))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@CanonicalLeaf.machine _v0))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine
  _v0)) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CanonicalLeaf.machine _v0) _v1 _v2 _v8 _v3))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@CanonicalLeaf.machine _v0)))))))))))))) := by
  exact @CanonicalLeaf.normal_work

-- Independent literal expected type for CanonicalLeaf.prepared.
noncomputable def PartACanonical.Types.p0236 :
(∀ (_v0 : (@Nat)),
(@CanonicalLeaf.Target.Body _v0)) := by
  exact @CanonicalLeaf.prepared

-- Complete literal proposition for CanonicalLeaf.prepared; original proof reused.
theorem PartACanonical.Surface.m0148 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (∀ (_v5 : (@Fin _v4)),
(@Bool))),
(∀ (_v6 : (∀ (_v6 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))),
(@Option.{0} (@Bool)))),
(∀ (_v7 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))),
(∀ (_v8 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v6 (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) _v3
  (@CanonicalLeaf.Target.Body._proof_3 _v1 _v2 _v3 _v4 _v7))) (@Option.none.{0} (@Bool)))),
(∀ (_v9 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v6 (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  _v7)) (@Option.none.{0} (@Bool)))),
(∀ (_v10 : (∀ (_v10 : (@Fin _v4)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v6 (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@HSub.hSub.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0}
  (@Nat) (@instSubNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Fin.val _v4 _v10))
  (@CanonicalLeaf.Target.Body._proof_4 _v1 _v2 _v3 _v4 _v7 _v10))) (@Option.some.{0} (@Bool) (@_v5 _v10))))),
(let _v11 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) := (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength
  _v1 _v2) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) _v7);
(let _v12 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@CanonicalLeaf.machine _v0)) _v1 _v2) := (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0)) _v1 _v2 (@CanonicalLeaf.entry _v0) _v11
  _v6);
(let _v13 : (@Bool) := (@dite.{(0 + 1)} (@Bool) (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) _v4) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v4) (fun
  (_v13 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v4)) =>
(@_v5 (@Fin.mk _v4 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v13))) (fun (_v13 : (@Not (@LT.lt.{0}
  (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v4))) =>
(@Bool.false)));
(@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@CanonicalLeaf.machine _v0)) _v1 _v2) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CanonicalLeaf.machine _v0) _v1 _v2
  (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v12) (@Pnp3.Complexity.Uniform.V1.Config.mk
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0)) _v1 _v2 (@ite.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0))) (@Eq.{(0 + 1)} (@Nat) _v4
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat _v4 (@OfNat.ofNat.{0} (@Nat) (0 :
  Nat) (@instOfNatNat (0 : Nat)))) (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@CanonicalLeaf.machine _v0))
  (@CanonicalLeaf.result _v0 _v13)) _v11 (@ite.{(0 + 1)} (∀ (_v14 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1
  _v2))),
(@Option.{0} (@Bool))) (@Eq.{(0 + 1)} (@Nat) _v4 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@instDecidableEqNat _v4 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) _v6 (@Function.update.{(0 + 1),
  (0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (fun (_v14 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))) =>
(@Option.{0} (@Bool))) (@instDecidableEqFin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) _v6 _v11 (@Option.some.{0}
  (@Bool) _v13))))) (@And (∀ (_v14 : (@Nat)),
(∀ (_v15 : (@LE.le.{0} (@Nat) (@instLENat) _v14 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))),
(@And (@LE.le.{0} (@Nat) (@instLENat) _v3 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)
  (@Pnp3.Complexity.Uniform.V1.Config.head (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0))
  _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CanonicalLeaf.machine _v0) _v1 _v2 _v14 _v12)))) (@LE.le.{0} (@Nat)
  (@instLENat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0)) _v1 _v2
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CanonicalLeaf.machine _v0) _v1 _v2 _v14 _v12))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v3 _v4) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))))) (@And (∀ (_v14 :
  (@Nat)),
(∀ (_v15 : (@LT.lt.{0} (@Nat) (@instLTNat) _v14 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))),
(@And (@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine
  _v0)) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CanonicalLeaf.machine _v0) _v1 _v2 _v14 _v12))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.accept (@CanonicalLeaf.machine _v0))) (@Ne.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine
  _v0)) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CanonicalLeaf.machine _v0) _v1 _v2 _v14 _v12))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@CanonicalLeaf.machine _v0)))))) (@And (∀ (_v14 : (@Nat)),
(∀ (_v15 : (@LT.lt.{0} (@Nat) (@instLTNat) _v14 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))),
(∀ (_v16 : (@Bool)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine
  _v0)) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CanonicalLeaf.machine _v0) _v1 _v2 _v14 _v12))
  (@CanonicalLeaf.result _v0 _v16))))) (@And (∀ (_v14 : (@Nat)),
(∀ (_v15 : (@LT.lt.{0} (@Nat) (@instLTNat) _v14 (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))),
(@Eq.{(0 + 1)} (∀ (_v16 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))),
(@Option.{0} (@Bool))) (@Pnp3.Complexity.Uniform.V1.Config.tape (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@CanonicalLeaf.machine _v0)) _v1 _v2 (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CanonicalLeaf.machine _v0) _v1 _v2
  _v14 _v12)) _v6))) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Nat) (@Bool))) (@Option.map.{0, 0}
  (@Pnp3.Models.Circuit _v4) (@Prod.{0, 0} (@Nat) (@Bool)) (fun (_v14 : (@Pnp3.Models.Circuit _v4)) =>
(@Prod.mk.{0, 0} (@Nat) (@Bool) (@Pnp3.Models.Circuit.size _v4 _v14) (@Pnp3.Models.Circuit.eval _v4 _v14 _v5)))
  (@Pnp4.Frontier.TreeCircuitWitnessCodec.decode (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v4 (fun
  (_v14 : (@Fin (@Pnp4.Frontier.TreeCircuitWitnessCodec.witnessBits (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v4)))
  =>
(@Bool.false)))) (@ite.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Nat) (@Bool))) (@Eq.{(0 + 1)} (@Nat) _v4 (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@instDecidableEqNat _v4 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat)))) (@Option.none.{0} (@Prod.{0, 0} (@Nat) (@Bool))) (@Option.some.{0} (@Prod.{0, 0} (@Nat) (@Bool))
  (@Prod.mk.{0, 0} (@Nat) (@Bool) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) _v13)))) (@And (@LE.le.{0}
  (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp4.Frontier.ContractExpansion.bitLength _v4) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))
  (@Cursor.Target.W _v0 _v4)) (∀ (_v14 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat
  (0 : Nat))) _v4)),
(@Eq.{(0 + 1)} (@Option.{0} (@Prod.{0, 0} (@Pnp3.Models.Circuit _v4) (@List.{0} (@Bool))))
  (@Pnp4.Frontier.ContractExpansion.decodeCircuitFull _v4 (@Pnp4.Frontier.ContractExpansion.bitLength _v4)
  (@List.replicate.{0} (@Bool) (@Cursor.Target.W _v0 _v4) (@Bool.false))) (@Option.some.{0} (@Prod.{0, 0}
  (@Pnp3.Models.Circuit _v4) (@List.{0} (@Bool))) (@Prod.mk.{0, 0} (@Pnp3.Models.Circuit _v4) (@List.{0} (@Bool))
  (@Pnp3.Models.Circuit.input _v4 (@Fin.mk _v4 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v14))
  (@List.replicate.{0} (@Bool) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat))
  (@Cursor.Target.W _v0 _v4) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) (@Pnp4.Frontier.ContractExpansion.bitLength _v4)))
  (@Bool.false))))))))))))))))))))))))))) := by
  exact @CanonicalLeaf.prepared

-- Independent literal expected type for CanonicalLeaf.repair138.
noncomputable def PartACanonical.Types.p0237 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0)))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step
  (@CanonicalLeaf.machine _v0) (@VirtualLeaf.embed _v0 (@Pnp3.Complexity.Uniform.V1.UniformTM.seqLeft
  (@IngressRepair.producer) (@Cursor.machine _v0) (@SmallIngress.q (@OfNat.ofNat.{0} (@Nat) (138 : Nat) (@instOfNatNat
  (138 : Nat)))))) (@Option.none.{0} (@Bool))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@CanonicalLeaf.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@CanonicalLeaf.machine _v0)) (@Prod.mk.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move) (@Option.none.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move.stay))))) := by
  exact @CanonicalLeaf.repair138

-- Complete literal proposition for CanonicalLeaf.repair138; original proof reused.
theorem PartACanonical.Surface.m0149 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0)))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step
  (@CanonicalLeaf.machine _v0) (@VirtualLeaf.embed _v0 (@Pnp3.Complexity.Uniform.V1.UniformTM.seqLeft
  (@IngressRepair.producer) (@Cursor.machine _v0) (@SmallIngress.q (@OfNat.ofNat.{0} (@Nat) (138 : Nat) (@instOfNatNat
  (138 : Nat)))))) (@Option.none.{0} (@Bool))) (@Prod.mk.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@CanonicalLeaf.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@CanonicalLeaf.machine _v0)) (@Prod.mk.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move) (@Option.none.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move.stay))))) := by
  exact @CanonicalLeaf.repair138

-- Independent literal expected type for CanonicalLeaf.repaired_rows.
noncomputable def PartACanonical.Types.p0238 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@IngressRepair.machine _v0)))),
(∀ (_v2 : (@Option.{0} (@Bool))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0)))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step
  (@CanonicalLeaf.machine _v0) (@VirtualLeaf.embed _v0 _v1) _v2) (@ite.{(0 + 1)} (@Prod.{0, 0} (@Fin (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@IngressRepair.machine _v0)) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))))) (@Prod.{0, 0} (@Option.{0}
  (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@And (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@IngressRepair.machine _v0))) _v1 (@VirtualLeaf.entry _v0)) (@Eq.{(0
  + 1)} (@Option.{0} (@Bool)) _v2 (@Option.none.{0} (@Bool)))) (@instDecidableAnd (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@IngressRepair.machine _v0))) _v1 (@VirtualLeaf.entry _v0)) (@Eq.{(0
  + 1)} (@Option.{0} (@Bool)) _v2 (@Option.none.{0} (@Bool))) (@instDecidableEqFin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@IngressRepair.machine _v0)) _v1 (@VirtualLeaf.entry _v0))
  (@Option.instDecidableEq.{0} (@Bool) (@instDecidableEqBool) _v2 (@Option.none.{0} (@Bool)))) (@Prod.mk.{0, 0} (@Fin
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@IngressRepair.machine _v0)) (@OfNat.ofNat.{0} (@Nat) (8 : Nat)
  (@instOfNatNat (8 : Nat))))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@VirtualLeaf.extra
  _v0 (@Fin.mk (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@of_decide_eq_true (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))) (@id.{0}
  (@Eq.{(0 + 1)} (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))))
  (@Bool.true)) (@Eq.refl.{(0 + 1)} (@Bool) (@Bool.true)))))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move) (@Option.none.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move.stay))) (@Prod.mk.{0, 0}
  (@Fin (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@IngressRepair.machine _v0)) (@OfNat.ofNat.{0} (@Nat) (8 : Nat)
  (@instOfNatNat (8 : Nat))))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@VirtualLeaf.embed
  _v0 (@Prod.fst.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@IngressRepair.machine _v0))) (@Prod.{0,
  0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step
  (@IngressRepair.machine _v0) _v1 _v2))) (@Prod.snd.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@IngressRepair.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@IngressRepair.machine _v0) _v1 _v2)))))))) := by
  exact @CanonicalLeaf.repaired_rows

-- Complete literal proposition for CanonicalLeaf.repaired_rows; original proof reused.
theorem PartACanonical.Surface.m0150 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@IngressRepair.machine _v0)))),
(∀ (_v2 : (@Option.{0} (@Bool))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0)))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step
  (@CanonicalLeaf.machine _v0) (@VirtualLeaf.embed _v0 _v1) _v2) (@ite.{(0 + 1)} (@Prod.{0, 0} (@Fin (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@IngressRepair.machine _v0)) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))))) (@Prod.{0, 0} (@Option.{0}
  (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@And (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@IngressRepair.machine _v0))) _v1 (@VirtualLeaf.entry _v0)) (@Eq.{(0
  + 1)} (@Option.{0} (@Bool)) _v2 (@Option.none.{0} (@Bool)))) (@instDecidableAnd (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@IngressRepair.machine _v0))) _v1 (@VirtualLeaf.entry _v0)) (@Eq.{(0
  + 1)} (@Option.{0} (@Bool)) _v2 (@Option.none.{0} (@Bool))) (@instDecidableEqFin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@IngressRepair.machine _v0)) _v1 (@VirtualLeaf.entry _v0))
  (@Option.instDecidableEq.{0} (@Bool) (@instDecidableEqBool) _v2 (@Option.none.{0} (@Bool)))) (@Prod.mk.{0, 0} (@Fin
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@IngressRepair.machine _v0)) (@OfNat.ofNat.{0} (@Nat) (8 : Nat)
  (@instOfNatNat (8 : Nat))))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@VirtualLeaf.extra
  _v0 (@Fin.mk (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@of_decide_eq_true (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))) (@id.{0}
  (@Eq.{(0 + 1)} (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))))
  (@Bool.true)) (@Eq.refl.{(0 + 1)} (@Bool) (@Bool.true)))))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move) (@Option.none.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move.stay))) (@Prod.mk.{0, 0}
  (@Fin (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@IngressRepair.machine _v0)) (@OfNat.ofNat.{0} (@Nat) (8 : Nat)
  (@instOfNatNat (8 : Nat))))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@VirtualLeaf.embed
  _v0 (@Prod.fst.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@IngressRepair.machine _v0))) (@Prod.{0,
  0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step
  (@IngressRepair.machine _v0) _v1 _v2))) (@Prod.snd.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@IngressRepair.machine _v0))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@IngressRepair.machine _v0) _v1 _v2)))))))) := by
  exact @CanonicalLeaf.repaired_rows

-- Independent literal expected type for CanonicalLeaf.result.
noncomputable def PartACanonical.Types.p0239 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Bool)),
(@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0))))) := by
  exact @CanonicalLeaf.result

-- Independent literal expected type for CanonicalLeaf.stall_reject.
noncomputable def PartACanonical.Types.p0240 :
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
  (2 : Nat)))))) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine
  _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@CanonicalLeaf.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat)
  (9216 : Nat) (@instOfNatNat (9216 : Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CanonicalLeaf.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) _v3 (@Pnp3.Complexity.Uniform.V1.initialConfig (@CanonicalLeaf.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat
  (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v1 _v2))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@CanonicalLeaf.machine _v0))) (@Eq.{(0 + 1)} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v1 _v2) (@Bool.false))))))))) := by
  exact @CanonicalLeaf.stall_reject

-- Complete literal proposition for CanonicalLeaf.stall_reject; original proof reused.
theorem PartACanonical.Surface.m0151 :
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
  (2 : Nat)))))) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine
  _v0))) (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@CanonicalLeaf.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat)
  (9216 : Nat) (@instOfNatNat (9216 : Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CanonicalLeaf.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) _v3 (@Pnp3.Complexity.Uniform.V1.initialConfig (@CanonicalLeaf.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat
  (9216 : Nat))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat
  (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v1 _v2))))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.reject (@CanonicalLeaf.machine _v0))) (@Eq.{(0 + 1)} (@Bool)
  (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 (@OfNat.ofNat.{0} (@Nat) (11 : Nat)
  (@instOfNatNat (11 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v1 _v2) (@Bool.false))))))))) := by
  exact @CanonicalLeaf.stall_reject

-- Independent literal expected type for CanonicalLeaf.table_delta.
noncomputable def PartACanonical.Types.p0241 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0)))),
(∀ (_v2 : (@Option.{0} (@Bool))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0)))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step
  (@CanonicalLeaf.machine _v0) _v1 _v2) (@CanonicalLeaf.table_delta.match_1.{(0 + 1)} (fun (_v3 : (@Option.{0} (@Bool)))
  =>
(@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0))) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)))) _v2 (fun (_v3 : (@Unit)) =>
(@Pnp3.Complexity.Uniform.V1.UniformTM.step (@VirtualLeaf.machine _v0) _v1 (@Option.none.{0} (@Bool)))) (fun (_v3 :
  (@Bool)) =>
(@ite.{(0 + 1)} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0)))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0))) _v1 (@VirtualLeaf.extra _v0 (@Fin.mk
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))) (@of_decide_eq_true (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))) (@id.{0} (@Eq.{(0 + 1)}
  (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))))) (@Bool.true)) (@Eq.refl.{(0 +
  1)} (@Bool) (@Bool.true))))))) (@instDecidableEqFin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@CanonicalLeaf.machine _v0)) _v1 (@VirtualLeaf.extra _v0 (@Fin.mk (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8
  : Nat))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@of_decide_eq_true (@LT.lt.{0} (@Nat)
  (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat)
  (@instOfNatNat (8 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@OfNat.ofNat.{0}
  (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))) (@id.{0} (@Eq.{(0 + 1)} (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat)
  (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat)
  (@instOfNatNat (8 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@OfNat.ofNat.{0}
  (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))))) (@Bool.true)) (@Eq.refl.{(0 + 1)} (@Bool) (@Bool.true))))))) (@Prod.mk.{0,
  0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0))) (@Prod.{0, 0} (@Option.{0}
  (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@VirtualLeaf.extra _v0 (@Fin.mk (@OfNat.ofNat.{0} (@Nat) (8 : Nat)
  (@instOfNatNat (8 : Nat))) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v3 (@Bool.true)) (@instDecidableEqBool _v3
  (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))) (@Bool.casesOn.{0} (fun (_v4 : (@Bool)) =>
(∀ (_v5 : (@Eq.{(0 + 1)} (@Bool) _v3 _v4)),
(@LT.lt.{0} (@Nat) (@instLTNat) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v3 (@Bool.true)) (@instDecidableEqBool
  _v3 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))))) _v3 (fun (_v4 : (@Eq.{(0 +
  1)} (@Bool) _v3 (@Bool.false))) =>
(@Eq.ndrec.{0, (0 + 1)} (@Bool) (@Bool.false) (fun (_v5 : (@Bool)) =>
(@LT.lt.{0} (@Nat) (@instLTNat) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v5 (@Bool.true)) (@instDecidableEqBool
  _v5 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))))) (@of_decide_eq_true
  (@LT.lt.{0} (@Nat) (@instLTNat) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) (@Bool.false) (@Bool.true))
  (@instDecidableEqBool (@Bool.false) (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 :
  Nat)))) (@Nat.decLt (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) (@Bool.false) (@Bool.true)) (@instDecidableEqBool
  (@Bool.false) (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))) (@id.{0} (@Eq.{(0 + 1)}
  (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat) (@instLTNat) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) (@Bool.false)
  (@Bool.true)) (@instDecidableEqBool (@Bool.false) (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat
  (8 : Nat)))) (@Nat.decLt (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) (@Bool.false) (@Bool.true)) (@instDecidableEqBool
  (@Bool.false) (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))))) (@Bool.true))
  (@Eq.refl.{(0 + 1)} (@Bool) (@Bool.true)))) _v3 (@Eq.symm.{(0 + 1)} (@Bool) _v3 (@Bool.false) _v4))) (fun (_v4 :
  (@Eq.{(0 + 1)} (@Bool) _v3 (@Bool.true))) =>
(@Eq.ndrec.{0, (0 + 1)} (@Bool) (@Bool.true) (fun (_v5 : (@Bool)) =>
(@LT.lt.{0} (@Nat) (@instLTNat) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v5 (@Bool.true)) (@instDecidableEqBool
  _v5 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))))) (@of_decide_eq_true
  (@LT.lt.{0} (@Nat) (@instLTNat) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) (@Bool.true) (@Bool.true))
  (@instDecidableEqBool (@Bool.true) (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 :
  Nat)))) (@Nat.decLt (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) (@Bool.true) (@Bool.true)) (@instDecidableEqBool
  (@Bool.true) (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))) (@id.{0} (@Eq.{(0 + 1)}
  (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat) (@instLTNat) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) (@Bool.true)
  (@Bool.true)) (@instDecidableEqBool (@Bool.true) (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat
  (8 : Nat)))) (@Nat.decLt (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) (@Bool.true) (@Bool.true)) (@instDecidableEqBool
  (@Bool.true) (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))))) (@Bool.true))
  (@Eq.refl.{(0 + 1)} (@Bool) (@Bool.true)))) _v3 (@Eq.symm.{(0 + 1)} (@Bool) _v3 (@Bool.true) _v4))) (@Eq.refl.{(0 + 1)}
  (@Bool) _v3)))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.some.{0} (@Bool) _v3)
  (@Pnp3.Complexity.Uniform.V1.Move.right))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@VirtualLeaf.machine _v0) _v1
  (@Option.some.{0} (@Bool) _v3))))))))) := by
  exact @CanonicalLeaf.table_delta

-- Complete literal proposition for CanonicalLeaf.table_delta; original proof reused.
theorem PartACanonical.Surface.m0152 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0)))),
(∀ (_v2 : (@Option.{0} (@Bool))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0)))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step
  (@CanonicalLeaf.machine _v0) _v1 _v2) (@CanonicalLeaf.table_delta.match_1.{(0 + 1)} (fun (_v3 : (@Option.{0} (@Bool)))
  =>
(@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0))) (@Prod.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)))) _v2 (fun (_v3 : (@Unit)) =>
(@Pnp3.Complexity.Uniform.V1.UniformTM.step (@VirtualLeaf.machine _v0) _v1 (@Option.none.{0} (@Bool)))) (fun (_v3 :
  (@Bool)) =>
(@ite.{(0 + 1)} (@Prod.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0)))
  (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))) (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0))) _v1 (@VirtualLeaf.extra _v0 (@Fin.mk
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))) (@of_decide_eq_true (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))) (@id.{0} (@Eq.{(0 + 1)}
  (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))))) (@Bool.true)) (@Eq.refl.{(0 +
  1)} (@Bool) (@Bool.true))))))) (@instDecidableEqFin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@CanonicalLeaf.machine _v0)) _v1 (@VirtualLeaf.extra _v0 (@Fin.mk (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8
  : Nat))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@of_decide_eq_true (@LT.lt.{0} (@Nat)
  (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat)
  (@instOfNatNat (8 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@OfNat.ofNat.{0}
  (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))) (@id.{0} (@Eq.{(0 + 1)} (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat)
  (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat)
  (@instOfNatNat (8 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@OfNat.ofNat.{0}
  (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))))) (@Bool.true)) (@Eq.refl.{(0 + 1)} (@Bool) (@Bool.true))))))) (@Prod.mk.{0,
  0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine _v0))) (@Prod.{0, 0} (@Option.{0}
  (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move)) (@VirtualLeaf.extra _v0 (@Fin.mk (@OfNat.ofNat.{0} (@Nat) (8 : Nat)
  (@instOfNatNat (8 : Nat))) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v3 (@Bool.true)) (@instDecidableEqBool _v3
  (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))) (@Bool.casesOn.{0} (fun (_v4 : (@Bool)) =>
(∀ (_v5 : (@Eq.{(0 + 1)} (@Bool) _v3 _v4)),
(@LT.lt.{0} (@Nat) (@instLTNat) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v3 (@Bool.true)) (@instDecidableEqBool
  _v3 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))))) _v3 (fun (_v4 : (@Eq.{(0 +
  1)} (@Bool) _v3 (@Bool.false))) =>
(@Eq.ndrec.{0, (0 + 1)} (@Bool) (@Bool.false) (fun (_v5 : (@Bool)) =>
(@LT.lt.{0} (@Nat) (@instLTNat) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v5 (@Bool.true)) (@instDecidableEqBool
  _v5 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))))) (@of_decide_eq_true
  (@LT.lt.{0} (@Nat) (@instLTNat) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) (@Bool.false) (@Bool.true))
  (@instDecidableEqBool (@Bool.false) (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 :
  Nat)))) (@Nat.decLt (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) (@Bool.false) (@Bool.true)) (@instDecidableEqBool
  (@Bool.false) (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))) (@id.{0} (@Eq.{(0 + 1)}
  (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat) (@instLTNat) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) (@Bool.false)
  (@Bool.true)) (@instDecidableEqBool (@Bool.false) (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat
  (8 : Nat)))) (@Nat.decLt (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) (@Bool.false) (@Bool.true)) (@instDecidableEqBool
  (@Bool.false) (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))))) (@Bool.true))
  (@Eq.refl.{(0 + 1)} (@Bool) (@Bool.true)))) _v3 (@Eq.symm.{(0 + 1)} (@Bool) _v3 (@Bool.false) _v4))) (fun (_v4 :
  (@Eq.{(0 + 1)} (@Bool) _v3 (@Bool.true))) =>
(@Eq.ndrec.{0, (0 + 1)} (@Bool) (@Bool.true) (fun (_v5 : (@Bool)) =>
(@LT.lt.{0} (@Nat) (@instLTNat) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) _v5 (@Bool.true)) (@instDecidableEqBool
  _v5 (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))))) (@of_decide_eq_true
  (@LT.lt.{0} (@Nat) (@instLTNat) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) (@Bool.true) (@Bool.true))
  (@instDecidableEqBool (@Bool.true) (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 :
  Nat)))) (@Nat.decLt (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) (@Bool.true) (@Bool.true)) (@instDecidableEqBool
  (@Bool.true) (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))) (@id.{0} (@Eq.{(0 + 1)}
  (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat) (@instLTNat) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) (@Bool.true)
  (@Bool.true)) (@instDecidableEqBool (@Bool.true) (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat
  (8 : Nat)))) (@Nat.decLt (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool) (@Bool.true) (@Bool.true)) (@instDecidableEqBool
  (@Bool.true) (@Bool.true)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))))) (@Bool.true))
  (@Eq.refl.{(0 + 1)} (@Bool) (@Bool.true)))) _v3 (@Eq.symm.{(0 + 1)} (@Bool) _v3 (@Bool.true) _v4))) (@Eq.refl.{(0 + 1)}
  (@Bool) _v3)))) (@Prod.mk.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Option.some.{0} (@Bool) _v3)
  (@Pnp3.Complexity.Uniform.V1.Move.right))) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@VirtualLeaf.machine _v0) _v1
  (@Option.some.{0} (@Bool) _v3))))))))) := by
  exact @CanonicalLeaf.table_delta

-- Independent literal expected type for CanonicalLeaf.tiny_accepted.
noncomputable def PartACanonical.Types.p0242 :
(let _v0 : (@Pnp3.Complexity.Uniform.V1.Bitstring (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))) := (fun
  (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))) =>
(@Bool.or (@Bool.or (@Bool.or (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))) _v0) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0
  : Nat)))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0}
  (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))) _v0) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))
  (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (7 :
  Nat) (@instOfNatNat (7 : Nat))) _v0) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))) (@BEq.beq.{0}
  (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (7 : Nat)
  (@instOfNatNat (7 : Nat))) _v0) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))));
(let _v1 : (@Pnp3.Complexity.Uniform.V1.Bitstring (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))) := (fun
  (_v1 : (@Fin (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))))) =>
(@Bool.or (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0}
  (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))
  (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (8 :
  Nat) (@instOfNatNat (8 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))));
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) _v0 _v1) (@Bool.true)))) := by
  exact @CanonicalLeaf.tiny_accepted

-- Complete literal proposition for CanonicalLeaf.tiny_accepted; original proof reused.
theorem PartACanonical.Surface.m0153 :
(let _v0 : (@Pnp3.Complexity.Uniform.V1.Bitstring (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))) := (fun
  (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))) =>
(@Bool.or (@Bool.or (@Bool.or (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))) _v0) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0
  : Nat)))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0}
  (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))) _v0) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))
  (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (7 :
  Nat) (@instOfNatNat (7 : Nat))) _v0) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))) (@BEq.beq.{0}
  (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (7 : Nat)
  (@instOfNatNat (7 : Nat))) _v0) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))));
(let _v1 : (@Pnp3.Complexity.Uniform.V1.Bitstring (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))) := (fun
  (_v1 : (@Fin (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))))) =>
(@Bool.or (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0}
  (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))
  (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (8 :
  Nat) (@instOfNatNat (8 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))));
(@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) _v0 _v1) (@Bool.true)))) := by
  exact @CanonicalLeaf.tiny_accepted

-- Independent literal expected type for CanonicalLeaf.tiny_raw.
noncomputable def PartACanonical.Types.p0243 :
(let _v0 : (@Pnp3.Complexity.Uniform.V1.Bitstring (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))) := (fun
  (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))) =>
(@Bool.or (@Bool.or (@Bool.or (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))) _v0) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0
  : Nat)))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0}
  (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))) _v0) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))
  (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (7 :
  Nat) (@instOfNatNat (7 : Nat))) _v0) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))) (@BEq.beq.{0}
  (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (7 : Nat)
  (@instOfNatNat (7 : Nat))) _v0) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))));
(let _v1 : (@Pnp3.Complexity.Uniform.V1.Bitstring (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))) := (fun
  (_v1 : (@Fin (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))))) =>
(@Bool.or (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0}
  (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))
  (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (8 :
  Nat) (@instOfNatNat (8 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v2 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v2 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4294967296 : Nat) (@instOfNatNat (4294967296 : Nat))) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat
  (5 : Nat)))))) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (7 : Nat)
  (@instOfNatNat (7 : Nat))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216
  : Nat) (@instOfNatNat (9216 : Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CanonicalLeaf.machine
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat (9216 : Nat))) _v2
  (@Pnp3.Complexity.Uniform.V1.initialConfig (@CanonicalLeaf.machine (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0
  : Nat)))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat)
  (@instOfNatNat (9216 : Nat))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair (@OfNat.ofNat.{0} (@Nat) (7 : Nat)
  (@instOfNatNat (7 : Nat))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) _v0 _v1))))
  (@CanonicalLeaf.result (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Bool.false))) (@Eq.{(0 + 1)}
  (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat (9216 : Nat)))) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (7 : Nat)
  (@instOfNatNat (7 : Nat))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216
  : Nat) (@instOfNatNat (9216 : Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CanonicalLeaf.machine
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat (9216 : Nat))) _v2
  (@Pnp3.Complexity.Uniform.V1.initialConfig (@CanonicalLeaf.machine (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0
  : Nat)))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat)
  (@instOfNatNat (9216 : Nat))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair (@OfNat.ofNat.{0} (@Nat) (7 : Nat)
  (@instOfNatNat (7 : Nat))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) _v0 _v1))))) (@OfNat.ofNat.{0}
  (@Nat) (20 : Nat) (@instOfNatNat (20 : Nat)))))))))) := by
  exact @CanonicalLeaf.tiny_raw

-- Complete literal proposition for CanonicalLeaf.tiny_raw; original proof reused.
theorem PartACanonical.Surface.m0154 :
(let _v0 : (@Pnp3.Complexity.Uniform.V1.Bitstring (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))) := (fun
  (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))) =>
(@Bool.or (@Bool.or (@Bool.or (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))) _v0) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0
  : Nat)))) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0}
  (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))) _v0) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))))
  (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (7 :
  Nat) (@instOfNatNat (7 : Nat))) _v0) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))) (@BEq.beq.{0}
  (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (7 : Nat)
  (@instOfNatNat (7 : Nat))) _v0) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))));
(let _v1 : (@Pnp3.Complexity.Uniform.V1.Bitstring (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))) := (fun
  (_v1 : (@Fin (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))))) =>
(@Bool.or (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0}
  (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))
  (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat) (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (8 :
  Nat) (@instOfNatNat (8 : Nat))) _v1) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))));
(@Exists.{(0 + 1)} (@Nat) (fun (_v2 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v2 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4294967296 : Nat) (@instOfNatNat (4294967296 : Nat))) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat
  (5 : Nat)))))) (@And (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))))) (@Pnp3.Complexity.Uniform.V1.Config.state
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (7 : Nat)
  (@instOfNatNat (7 : Nat))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216
  : Nat) (@instOfNatNat (9216 : Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CanonicalLeaf.machine
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat (9216 : Nat))) _v2
  (@Pnp3.Complexity.Uniform.V1.initialConfig (@CanonicalLeaf.machine (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0
  : Nat)))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat)
  (@instOfNatNat (9216 : Nat))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair (@OfNat.ofNat.{0} (@Nat) (7 : Nat)
  (@instOfNatNat (7 : Nat))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) _v0 _v1))))
  (@CanonicalLeaf.result (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@Bool.false))) (@Eq.{(0 + 1)}
  (@Nat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat (9216 : Nat)))) (@Pnp3.Complexity.Uniform.V1.Config.head
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@CanonicalLeaf.machine (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (7 : Nat)
  (@instOfNatNat (7 : Nat))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216
  : Nat) (@instOfNatNat (9216 : Nat))) (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@CanonicalLeaf.machine
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat) (@instOfNatNat (9216 : Nat))) _v2
  (@Pnp3.Complexity.Uniform.V1.initialConfig (@CanonicalLeaf.machine (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0
  : Nat)))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 :
  Nat))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (9216 : Nat)
  (@instOfNatNat (9216 : Nat))) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair (@OfNat.ofNat.{0} (@Nat) (7 : Nat)
  (@instOfNatNat (7 : Nat))) (@OfNat.ofNat.{0} (@Nat) (8 : Nat) (@instOfNatNat (8 : Nat))) _v0 _v1))))) (@OfNat.ofNat.{0}
  (@Nat) (20 : Nat) (@instOfNatNat (20 : Nat)))))))))) := by
  exact @CanonicalLeaf.tiny_raw

-- Independent literal expected type for CappedWeight.Target.Cap.
noncomputable def PartACanonical.Types.p0244 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (@Nat)),
(Sort 0))))))))) := by
  exact @CappedWeight.Target.Cap

-- Independent literal expected type for CappedWeight.Target.FirstProduct.
noncomputable def PartACanonical.Types.p0245 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Nat)),
(∀ (_v6 : (@Nat)),
(∀ (_v7 : (∀ (_v7 : (@Nat)),
(@Option.{0} (@Bool)))),
(Sort 0))))))))) := by
  exact @CappedWeight.Target.FirstProduct

-- Independent literal expected type for CappedWeight.Target.FullRaw.
noncomputable def PartACanonical.Types.p0246 :
(∀ (_v0 : (@Nat)),
(Sort 0)) := by
  exact @CappedWeight.Target.FullRaw

-- Independent literal expected type for CappedWeight.Target.RawProduct.
noncomputable def PartACanonical.Types.p0247 :
(∀ (_v0 : (@Nat)),
(Sort 0)) := by
  exact @CappedWeight.Target.RawProduct

-- Independent literal expected type for CappedWeight.Target.image.
noncomputable def PartACanonical.Types.p0248 :
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
(@Option.{0} (@Bool))))))))))))) := by
  exact @CappedWeight.Target.image

-- Independent literal expected type for CappedWeight.Target.image.eq_1.
noncomputable def PartACanonical.Types.p0249 :
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
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@CappedWeight.Target.image _v0 _v1 _v2 _v3 _v4 _v5 _v6 _v7 _v8 _v9 _v10) (@ite.{(0
  + 1)} (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v1 _v10) (@LT.lt.{0} (@Nat) (@instLTNat) _v10
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))
  (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) _v1 _v10) (@LT.lt.{0} (@Nat) (@instLTNat) _v10 (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Nat.decLt _v1 _v10)
  (@Nat.decLt _v10 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))))) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v9) _v10) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v9) _v10))) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And
  (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) _v2) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))
  _v10) (@LT.lt.{0} (@Nat) (@instLTNat) _v10 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) _v2)
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v10) (@LT.lt.{0} (@Nat) (@instLTNat) _v10
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))
  (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 _v4) _v2) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v10) (@Nat.decLt _v10
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))))
  (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat) (@instLENat) _v10 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) _v2) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) _v5)) (@Nat.decLe _v10 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v3 _v4) _v2) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v5)))) (@ite.{(0 +
  1)} (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)) _v2)
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v10) (@LT.lt.{0} (@Nat) (@instLTNat) _v10
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))))
  (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))) _v10) (@LT.lt.{0} (@Nat) (@instLTNat) _v10 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))
  _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))) (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v10) (@Nat.decLt _v10 (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))) (@Option.some.{0}
  (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat) (@instLENat) _v10 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))) _v6)) (@Nat.decLe _v10 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))) _v6)))) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))
  _v10) (@LT.lt.{0} (@Nat) (@instLTNat) _v10 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat)
  (6 : Nat) (@instOfNatNat (6 : Nat)))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))
  _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) _v10) (@LT.lt.{0} (@Nat) (@instLTNat) _v10
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))
  (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))
  _v10) (@Nat.decLt _v10 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (6 : Nat)
  (@instOfNatNat (6 : Nat)))))) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat) (@instLENat) _v10
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))
  _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) _v7)) (@Nat.decLe _v10 (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v4)) _v2)
  (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) _v7)))) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And
  (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (6 :
  Nat) (@instOfNatNat (6 : Nat)))) _v10) (@LT.lt.{0} (@Nat) (@instLTNat) _v10 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v4)) _v2)
  (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))
  _v10) (@LT.lt.{0} (@Nat) (@instLTNat) _v10 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat)
  (7 : Nat) (@instOfNatNat (7 : Nat))))) (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat)
  (6 : Nat) (@instOfNatNat (6 : Nat)))) _v10) (@Nat.decLt _v10 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v4)) _v2)
  (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))))) (@Option.some.{0} (@Bool) (@Decidable.decide
  (@LE.le.{0} (@Nat) (@instLENat) _v10 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))
  _v8)) (@Nat.decLe _v10 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) _v8)))) (@_v0
  _v10)))))))))))))))))) := by
  exact @CappedWeight.Target.image.eq_1

-- Complete literal proposition for CappedWeight.Target.image.eq_1; original proof reused.
theorem PartACanonical.Surface.m0155 :
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
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@CappedWeight.Target.image _v0 _v1 _v2 _v3 _v4 _v5 _v6 _v7 _v8 _v9 _v10) (@ite.{(0
  + 1)} (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v1 _v10) (@LT.lt.{0} (@Nat) (@instLTNat) _v10
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))
  (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) _v1 _v10) (@LT.lt.{0} (@Nat) (@instLTNat) _v10 (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Nat.decLt _v1 _v10)
  (@Nat.decLt _v10 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1
  : Nat)))))) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat) (@instLENat) (@HSub.hSub.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v9) _v10) (@Nat.decLe (@HSub.hSub.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v9) _v10))) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And
  (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) _v2) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))
  _v10) (@LT.lt.{0} (@Nat) (@instLTNat) _v10 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) _v2)
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v10) (@LT.lt.{0} (@Nat) (@instLTNat) _v10
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))
  (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 _v4) _v2) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v10) (@Nat.decLt _v10
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))))
  (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat) (@instLENat) _v10 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) _v2) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat)))) _v5)) (@Nat.decLe _v10 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v3 _v4) _v2) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v5)))) (@ite.{(0 +
  1)} (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)) _v2)
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v10) (@LT.lt.{0} (@Nat) (@instLTNat) _v10
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))))
  (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))) _v10) (@LT.lt.{0} (@Nat) (@instLTNat) _v10 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))
  _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))) (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) _v10) (@Nat.decLt _v10 (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))))) (@Option.some.{0}
  (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat) (@instLENat) _v10 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))) _v6)) (@Nat.decLe _v10 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))) _v6)))) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))
  _v10) (@LT.lt.{0} (@Nat) (@instLTNat) _v10 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat)
  (6 : Nat) (@instOfNatNat (6 : Nat)))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))
  _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) _v10) (@LT.lt.{0} (@Nat) (@instLTNat) _v10
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))))
  (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))))
  _v10) (@Nat.decLt _v10 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (6 : Nat)
  (@instOfNatNat (6 : Nat)))))) (@Option.some.{0} (@Bool) (@Decidable.decide (@LE.le.{0} (@Nat) (@instLENat) _v10
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))
  _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) _v7)) (@Nat.decLe _v10 (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v4)) _v2)
  (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat)))) _v7)))) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And
  (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (6 :
  Nat) (@instOfNatNat (6 : Nat)))) _v10) (@LT.lt.{0} (@Nat) (@instLTNat) _v10 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v4)) _v2)
  (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))))) (@instDecidableAnd (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))
  _v10) (@LT.lt.{0} (@Nat) (@instLTNat) _v10 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat)
  (7 : Nat) (@instOfNatNat (7 : Nat))))) (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat)
  (6 : Nat) (@instOfNatNat (6 : Nat)))) _v10) (@Nat.decLt _v10 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v4)) _v2)
  (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))))) (@Option.some.{0} (@Bool) (@Decidable.decide
  (@LE.le.{0} (@Nat) (@instLENat) _v10 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat))))
  _v8)) (@Nat.decLe _v10 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat))) _v4)) _v2) (@OfNat.ofNat.{0} (@Nat) (6 : Nat) (@instOfNatNat (6 : Nat)))) _v8)))) (@_v0
  _v10)))))))))))))))))) := by
  exact @CappedWeight.Target.image.eq_1

-- Independent literal expected type for CappedWeight.accepted_first_product.
noncomputable def PartACanonical.Types.p0250 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v0)),
(@CappedWeight.Target.RawProduct _v0))) := by
  exact @CappedWeight.accepted_first_product

-- Complete literal proposition for CappedWeight.accepted_first_product; original proof reused.
theorem PartACanonical.Surface.m0156 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v0)),
(∀ {_v2 : (@Nat)},
(∀ {_v3 : (@Nat)},
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v2)),
(∀ (_v5 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v3)),
(∀ (_v6 : (@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v2
  _v3 _v4 _v5) (@Bool.true))),
(@Exists.{(0 + 1)} (@Sigma.{0, 0} (@Nat) (fun (_v7 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v7)))) (fun (_v7 : (@Sigma.{0, 0} (@Nat) (fun (_v7 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v7))))) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Sigma.{0, 0} (@Nat) (fun (_v8 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v8))))) (@Pnp4.Frontier.ContractExpansion.contentInput?
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v2 _v3) (@Fin.append.{(0 + 1)} _v2 _v3 (@Bool) _v4 _v5)) (@Option.some.{0} (@Sigma.{0, 0} (@Nat) (fun
  (_v8 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v8)))) _v7)) (@And (@LE.le.{0} (@Nat) (@instLENat)
  (@Pnp3.Models.Partial.tableLen (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v8))) _v7)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v8 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v8))) _v7))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v3)) (@Exists.{(0 + 1)} (@Nat) (fun (_v8 : (@Nat)) =>
(@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v2 _v3) _v8) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v9))) _v7)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v9))) _v7))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2
  _v3)))) (fun (_v9 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v2 _v3) _v8) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v9))) _v7)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v9))) _v7))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2
  _v3))))) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros?
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v3) (@Fin.append.{(0 + 1)} _v2 _v3
  (@Bool) _v4 _v5)) (@Option.some.{0} (@Nat) _v8)) (let _v10 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v3);
(let _v11 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3);
(let _v12 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation _v11);
(let _v13 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v11);
(let _v14 : (@Nat) := (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v14))) _v7)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v14 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v14))) _v7));
(let _v15 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 _v8) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat))));
(let _v16 : (∀ (_v16 : (@Nat)),
(@Option.{0} (@Bool))) := (@Body.extend (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3) _v12
  (@Body.installedTape (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3) _v12 (@SmallIngress.prepared _v2 _v3
  _v12 _v4 _v5 _v8 _v14) _v15 _v14));
(let _v17 : (∀ (_v17 : (@Nat)),
(@Option.{0} (@Bool))) := (@Stream.Target.image _v16 _v10 _v8 _v14 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v8)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v14) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v14) (@Bool.false));
(let _v18 : (@Nat) := (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v8)) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v14)) _v10);
(let _v19 : (@Nat) := (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v10 _v18);
(let _v20 : (∀ (_v20 : (@Nat)),
(@Option.{0} (@Bool))) := (@CappedWorkspace.Target.image (@SuffixCap.Target.image _v17 _v13 _v19) _v15 _v14 _v13 _v19);
(let _v21 : (∀ (_v21 : (@Nat)),
(@Option.{0} (@Bool))) := (@RuntimeBitLength.Target.fullImage _v20 _v15 _v14 _v13 _v19);
(let _v22 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3) _v12) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3) _v12 (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair
  _v2 _v3 _v4 _v5));
(@And (∀ (_v23 : (@Eq.{(0 + 1)} (@Nat) _v18 _v10)),
(@Exists.{(0 + 1)} (@Nat) (fun (_v24 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v24 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (67108864 : Nat) (@instOfNatNat (67108864 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@And (@LE.le.{0} (@Nat) (@instLENat) _v10
  (@Cursor.Target.M _v0 _v14 _v8)) (@And (@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v3) (@Fin.append.{(0 + 1)} _v2 _v3 (@Bool) _v4 _v5)
  (@Cursor.Target.M _v0 _v14 _v8)) (@Bool.false)) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3) _v12) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3) _v12 _v24 _v22)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@SmallIngress.producer) (@Cursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2
  _v3)) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2
  _v3)) (@Cursor.mReady _v0 (@Fin.mk (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@CappedWeight.Target.RawProduct._proof_3))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2
  _v3))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v10 _v8) _v14) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v9) (fun (_v25 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2
  _v3))))) =>
(@_v17 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2
  _v3))) _v25)))))))))))) (∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) _v18 _v10)),
(@Exists.{(0 + 1)} (@Nat) (fun (_v24 : (@Nat)) =>
(@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@ite.{(0 + 1)} (@Nat) (@LE.le.{0} (@Nat) (@instLENat)
  (@Pnp4.Frontier.ContractExpansion.bitLength _v14) _v19) (@Nat.decLe (@Pnp4.Frontier.ContractExpansion.bitLength _v14)
  _v19) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v13 _v19) _v14) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12)) (fun (_v25 : (@LT.lt.{0} (@Nat) (@instLTNat) (@ite.{(0 + 1)} (@Nat)
  (@LE.le.{0} (@Nat) (@instLENat) (@Pnp4.Frontier.ContractExpansion.bitLength _v14) _v19) (@Nat.decLe
  (@Pnp4.Frontier.ContractExpansion.bitLength _v14) _v19) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0}
  (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 _v19) _v14) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12))) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v24 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (67108864 : Nat) (@instOfNatNat (67108864 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@And (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12)) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3) _v12) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3) _v12 _v24 _v22)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@SmallIngress.producer) (@Cursor.machine _v0) _v11 _v12
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0)) _v11
  _v12 (@Cursor.q _v0 (@ite.{(0 + 1)} (@Nat) (@LE.le.{0} (@Nat) (@instLENat) (@Pnp4.Frontier.ContractExpansion.bitLength
  _v14) _v19) (@Nat.decLe (@Pnp4.Frontier.ContractExpansion.bitLength _v14) _v19) (@OfNat.ofNat.{0} (@Nat) (329 : Nat)
  (@instOfNatNat (329 : Nat))) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) (@HMod.hMod.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMod.{0} (@Nat) (@Nat.instMod)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  _v19 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2
  : Nat)))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@instDecidableEqNat (@HMod.hMod.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMod.{0} (@Nat) (@Nat.instMod)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v19 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat)
  (250 : Nat) (@instOfNatNat (250 : Nat))) (@OfNat.ofNat.{0} (@Nat) (304 : Nat) (@instOfNatNat (304 : Nat)))))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12) (@ite.{(0 + 1)} (@Nat) (@LE.le.{0} (@Nat) (@instLENat)
  (@Pnp4.Frontier.ContractExpansion.bitLength _v14) _v19) (@Nat.decLe (@Pnp4.Frontier.ContractExpansion.bitLength _v14)
  _v19) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v13 _v19) _v14) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))) _v25) (fun (_v26 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12))) =>
(@ite.{(0 + 1)} (∀ (_v27 : (@Nat)),
(@Option.{0} (@Bool))) (@LE.le.{0} (@Nat) (@instLENat) (@Pnp4.Frontier.ContractExpansion.bitLength _v14) _v19)
  (@Nat.decLe (@Pnp4.Frontier.ContractExpansion.bitLength _v14) _v19) (@AllArityBitLength.Target.seedImage _v21 _v13 _v19
  _v14) _v21 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12) _v26)))))) (@And (∀ (_v26 : (@Nat)),
(∀ (_v27 : (@LT.lt.{0} (@Nat) (@instLTNat) _v26 _v24)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3) _v12 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3) _v12 _v26 _v22))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0) (@Cursor.q _v0
  (@OfNat.ofNat.{0} (@Nat) (329 : Nat) (@instOfNatNat (329 : Nat)))))))) (@And (∀ (_v26 : (@LT.lt.{0} (@Nat) (@instLTNat)
  _v19 (@Pnp4.Frontier.ContractExpansion.bitLength _v14))),
(@LT.lt.{0} (@Nat) (@instLTNat) _v10 (@Cursor.Target.M _v0 _v14 _v8))) (∀ (_v26 : (@LE.le.{0} (@Nat) (@instLENat)
  (@Pnp4.Frontier.ContractExpansion.bitLength _v14) _v19)),
(∀ (_v27 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0}
  (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12))),
(@Exists.{(0 + 1)} (@Nat) (fun (_v28 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v28 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (1024 : Nat) (@instOfNatNat (1024 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 _v19)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 :
  Nat)))))) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3) _v12)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3) _v12 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v24 _v28) _v22) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight
  (@SmallIngress.producer) (@Cursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3) _v12
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3) _v12 (@Cursor.q _v0 (@ite.{(0 + 1)} (@Nat) (@LE.le.{0}
  (@Nat) (@instLENat) _v14 _v19) (@Nat.decLe _v14 _v19) (@OfNat.ofNat.{0} (@Nat) (411 : Nat) (@instOfNatNat (411 : Nat)))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (798 : Nat)
  (@instOfNatNat (798 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (93 : Nat) (@instOfNatNat (93 : Nat))) _v0)))) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3) _v12) (@ite.{(0 + 1)} (@Nat) (@LE.le.{0} (@Nat)
  (@instLENat) _v14 _v19) (@Nat.decLe _v14 _v19) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0}
  (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v13 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))
  (@CappedWeight.Target.RawProduct._proof_4 _v0 _v2 _v3 _v7 _v8 _v27)) (fun (_v29 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3) _v12))) =>
(@CappedWeight.Target.image (@AllArityBitLength.Target.seedImage _v21 _v13 _v19 _v14) _v15 _v14 _v13 _v19
  (@Pnp4.Frontier.ContractExpansion.bitLength _v14) (@ite.{(0 + 1)} (@Nat) (@LE.le.{0} (@Nat) (@instLENat) _v14 _v19)
  (@Nat.decLe _v14 _v19) _v14 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@ite.{(0 + 1)} (@Nat)
  (@LE.le.{0} (@Nat) (@instLENat) _v14 _v19) (@Nat.decLe _v14 _v19) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) _v19) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@ite.{(0 + 1)} (@Nat) (@LE.le.{0} (@Nat)
  (@instLENat) _v14 _v19) (@Nat.decLe _v14 _v19) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v19 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3) _v12) _v29)))))) (@And (@LE.le.{0} (@Nat) (@instLENat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v24 _v28) (@HMul.hMul.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (268435456 : Nat) (@instOfNatNat (268435456
  : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v11
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@And (∀ (_v29 : (@Nat)),
(∀ (_v30 : (@LT.lt.{0} (@Nat) (@instLTNat) _v29 _v28)),
(@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3) _v12
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3) _v12 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v24 _v29) _v22))) (@OfNat.ofNat.{0} (@Nat) (699 : Nat) (@instOfNatNat (699 :
  Nat)))))) (∀ (_v29 : (@LT.lt.{0} (@Nat) (@instLTNat) _v19 _v14)),
(@LT.lt.{0} (@Nat) (@instLTNat) _v10 (@Cursor.Target.M _v0 _v14 _v8))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @CappedWeight.accepted_first_product

-- Independent literal expected type for CappedWeight.canonical_outcome.
noncomputable def PartACanonical.Types.p0251 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v0)),
(∀ (_v2 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(∀ (_v3 : (@Bool)),
(let _v4 : (@Pnp4.Frontier.TreeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) :=
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0));
(let _v5 : (@Nat) := (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly
  _v0) _v4 (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v2));
(let _v6 : (@Nat) := (@Pnp3.ComplexityInterfaces.certificateLength _v5 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat))));
(let _v7 : (@Pnp4.Frontier.ContractExpansion.PrefixBitVec (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v4 (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat))) _v2))) := (@Pnp4.Frontier.ContractExpansion.zeroPrefixQueryValue
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v4 (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat))) _v2) (fun (_v7 : (@Fin (@Pnp3.Models.Partial.tableLen (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))) _v2)))) =>
_v3));
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v6) (fun (_v8 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v6))
  =>
(@And (@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v5 _v6
  _v7 _v8) (@Bool.true)) (@Exists.{(0 + 1)} (@Nat) (fun (_v9 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v9 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (268435456 : Nat) (@instOfNatNat (268435456 : Nat))) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v5
  _v6) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4
  : Nat)))))) (let _v10 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v4 (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v2)) _v6)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v5
  _v6))) := (@Pnp3.Complexity.Uniform.V1.initialConfig (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v4 (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat))) _v2)) _v6) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v5 _v6)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v4 (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v2)) _v6 _v7 _v8));
(@Or (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v4 (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat))) _v2)) _v6) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v5 _v6)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v4 (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v2)) _v6)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v5
  _v6)) _v9 _v10)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0)
  (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (411 : Nat) (@instOfNatNat (411 : Nat)))))) (@Or (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v4 (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat))) _v2)) _v6) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v5 _v6)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v4 (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v2)) _v6)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v5
  _v6)) _v9 _v10)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0)
  (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat)
  (798 : Nat) (@instOfNatNat (798 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (93 : Nat) (@instOfNatNat (93 : Nat))) _v0))))) (@Or (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v4 (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat))) _v2)) _v6) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v5 _v6)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v4 (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v2)) _v6)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v5
  _v6)) _v9 _v10)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0)
  (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (250 : Nat) (@instOfNatNat (250 : Nat)))))) (@Or (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v4 (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat))) _v2)) _v6) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v5 _v6)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v4 (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v2)) _v6)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v5
  _v6)) _v9 _v10)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0)
  (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (304 : Nat) (@instOfNatNat (304 : Nat)))))) (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v4 (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat))) _v2)) _v6) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v5 _v6)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v4 (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v2)) _v6)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v5
  _v6)) _v9 _v10)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0)
  (@Cursor.mReady _v0 (@Fin.mk (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))) (@of_decide_eq_true (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@id.{0}
  (@Eq.{(0 + 1)} (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))))
  (@Bool.true)) (@Eq.refl.{(0 + 1)} (@Bool) (@Bool.true))))))))))))))))))))))))))) := by
  exact @CappedWeight.canonical_outcome

-- Complete literal proposition for CappedWeight.canonical_outcome; original proof reused.
theorem PartACanonical.Surface.m0157 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v0)),
(∀ (_v2 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(∀ (_v3 : (@Bool)),
(let _v4 : (@Pnp4.Frontier.TreeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) :=
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0));
(let _v5 : (@Nat) := (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly
  _v0) _v4 (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v2));
(let _v6 : (@Nat) := (@Pnp3.ComplexityInterfaces.certificateLength _v5 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat))));
(let _v7 : (@Pnp4.Frontier.ContractExpansion.PrefixBitVec (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v4 (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat))) _v2))) := (@Pnp4.Frontier.ContractExpansion.zeroPrefixQueryValue
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v4 (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat))) _v2) (fun (_v7 : (@Fin (@Pnp3.Models.Partial.tableLen (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))) _v2)))) =>
_v3));
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v6) (fun (_v8 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v6))
  =>
(@And (@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v5 _v6
  _v7 _v8) (@Bool.true)) (@Exists.{(0 + 1)} (@Nat) (fun (_v9 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v9 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (268435456 : Nat) (@instOfNatNat (268435456 : Nat))) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v5
  _v6) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4
  : Nat)))))) (let _v10 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v4 (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v2)) _v6)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v5
  _v6))) := (@Pnp3.Complexity.Uniform.V1.initialConfig (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v4 (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat))) _v2)) _v6) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v5 _v6)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v4 (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v2)) _v6 _v7 _v8));
(@Or (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v4 (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat))) _v2)) _v6) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v5 _v6)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v4 (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v2)) _v6)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v5
  _v6)) _v9 _v10)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0)
  (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (411 : Nat) (@instOfNatNat (411 : Nat)))))) (@Or (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v4 (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat))) _v2)) _v6) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v5 _v6)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v4 (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v2)) _v6)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v5
  _v6)) _v9 _v10)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0)
  (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat)
  (798 : Nat) (@instOfNatNat (798 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (93 : Nat) (@instOfNatNat (93 : Nat))) _v0))))) (@Or (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v4 (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat))) _v2)) _v6) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v5 _v6)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v4 (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v2)) _v6)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v5
  _v6)) _v9 _v10)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0)
  (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (250 : Nat) (@instOfNatNat (250 : Nat)))))) (@Or (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v4 (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat))) _v2)) _v6) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v5 _v6)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v4 (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v2)) _v6)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v5
  _v6)) _v9 _v10)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0)
  (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (304 : Nat) (@instOfNatNat (304 : Nat)))))) (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v4 (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat))) _v2)) _v6) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v5 _v6)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v4 (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v2)) _v6)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v5
  _v6)) _v9 _v10)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0)
  (@Cursor.mReady _v0 (@Fin.mk (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))) (@of_decide_eq_true (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@id.{0}
  (@Eq.{(0 + 1)} (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))))
  (@Bool.true)) (@Eq.refl.{(0 + 1)} (@Bool) (@Bool.true))))))))))))))))))))))))))) := by
  exact @CappedWeight.canonical_outcome

-- Independent literal expected type for CappedWeight.check_accepted_first_product.
noncomputable def PartACanonical.Types.p0252 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v0)),
(∀ {_v2 : (@Nat)},
(∀ {_v3 : (@Nat)},
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v2)),
(∀ (_v5 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v3)),
(∀ (_v6 : (@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v2
  _v3 _v4 _v5) (@Bool.true))),
(@Exists.{(0 + 1)} (@Sigma.{0, 0} (@Nat) (fun (_v7 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v7)))) (fun (_v7 : (@Sigma.{0, 0} (@Nat) (fun (_v7 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v7))))) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Sigma.{0, 0} (@Nat) (fun (_v8 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v8))))) (@Pnp4.Frontier.ContractExpansion.contentInput?
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v2 _v3) (@Fin.append.{(0 + 1)} _v2 _v3 (@Bool) _v4 _v5)) (@Option.some.{0} (@Sigma.{0, 0} (@Nat) (fun
  (_v8 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v8)))) _v7)) (@And (@LE.le.{0} (@Nat) (@instLENat)
  (@Pnp3.Models.Partial.tableLen (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v8))) _v7)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v8 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v8))) _v7))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v3)) (@Exists.{(0 + 1)} (@Nat) (fun (_v8 : (@Nat)) =>
(@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v2 _v3) _v8) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v9))) _v7)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v9))) _v7))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2
  _v3)))) (fun (_v9 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v2 _v3) _v8) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v9))) _v7)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v9))) _v7))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2
  _v3))))) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros?
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v3) (@Fin.append.{(0 + 1)} _v2 _v3
  (@Bool) _v4 _v5)) (@Option.some.{0} (@Nat) _v8)) (let _v10 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v3);
(let _v11 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3);
(let _v12 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation _v11);
(let _v13 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v11);
(let _v14 : (@Nat) := (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v14))) _v7)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v14 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v14))) _v7));
(let _v15 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 _v8) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat))));
(let _v16 : (∀ (_v16 : (@Nat)),
(@Option.{0} (@Bool))) := (@Body.extend (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3) _v12
  (@Body.installedTape (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3) _v12 (@SmallIngress.prepared _v2 _v3
  _v12 _v4 _v5 _v8 _v14) _v15 _v14));
(let _v17 : (∀ (_v17 : (@Nat)),
(@Option.{0} (@Bool))) := (@Stream.Target.image _v16 _v10 _v8 _v14 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v8)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v14) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v14) (@Bool.false));
(let _v18 : (@Nat) := (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v8)) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v14)) _v10);
(let _v19 : (@Nat) := (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v10 _v18);
(let _v20 : (∀ (_v20 : (@Nat)),
(@Option.{0} (@Bool))) := (@CappedWorkspace.Target.image (@SuffixCap.Target.image _v17 _v13 _v19) _v15 _v14 _v13 _v19);
(let _v21 : (∀ (_v21 : (@Nat)),
(@Option.{0} (@Bool))) := (@RuntimeBitLength.Target.fullImage _v20 _v15 _v14 _v13 _v19);
(let _v22 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3) _v12) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3) _v12 (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair
  _v2 _v3 _v4 _v5));
(@And (∀ (_v23 : (@Eq.{(0 + 1)} (@Nat) _v18 _v10)),
(@Exists.{(0 + 1)} (@Nat) (fun (_v24 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v24 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (67108864 : Nat) (@instOfNatNat (67108864 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@And (@LE.le.{0} (@Nat) (@instLENat) _v10
  (@Cursor.Target.M _v0 _v14 _v8)) (@And (@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v3) (@Fin.append.{(0 + 1)} _v2 _v3 (@Bool) _v4 _v5)
  (@Cursor.Target.M _v0 _v14 _v8)) (@Bool.false)) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3) _v12) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3) _v12 _v24 _v22)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@SmallIngress.producer) (@Cursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2
  _v3)) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2
  _v3)) (@Cursor.mReady _v0 (@Fin.mk (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@of_decide_eq_true (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Nat.decLt
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 :
  Nat)))) (@id.{0} (@Eq.{(0 + 1)} (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Nat.decLt
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 :
  Nat))))) (@Bool.true)) (@Eq.refl.{(0 + 1)} (@Bool) (@Bool.true)))))) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2
  _v3))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v10 _v8) _v14) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v9) (fun (_v25 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2
  _v3))))) =>
(@_v17 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2
  _v3))) _v25)))))))))))) (∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) _v18 _v10)),
(@Exists.{(0 + 1)} (@Nat) (fun (_v24 : (@Nat)) =>
(@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@ite.{(0 + 1)} (@Nat) (@LE.le.{0} (@Nat) (@instLENat)
  (@Pnp4.Frontier.ContractExpansion.bitLength _v14) _v19) (@Nat.decLe (@Pnp4.Frontier.ContractExpansion.bitLength _v14)
  _v19) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v13 _v19) _v14) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12)) (fun (_v25 : (@LT.lt.{0} (@Nat) (@instLTNat) (@ite.{(0 + 1)} (@Nat)
  (@LE.le.{0} (@Nat) (@instLENat) (@Pnp4.Frontier.ContractExpansion.bitLength _v14) _v19) (@Nat.decLe
  (@Pnp4.Frontier.ContractExpansion.bitLength _v14) _v19) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0}
  (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 _v19) _v14) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12))) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v24 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (67108864 : Nat) (@instOfNatNat (67108864 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@And (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12)) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3) _v12) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3) _v12 _v24 _v22)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@SmallIngress.producer) (@Cursor.machine _v0) _v11 _v12
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0)) _v11
  _v12 (@Cursor.q _v0 (@ite.{(0 + 1)} (@Nat) (@LE.le.{0} (@Nat) (@instLENat) (@Pnp4.Frontier.ContractExpansion.bitLength
  _v14) _v19) (@Nat.decLe (@Pnp4.Frontier.ContractExpansion.bitLength _v14) _v19) (@OfNat.ofNat.{0} (@Nat) (329 : Nat)
  (@instOfNatNat (329 : Nat))) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) (@HMod.hMod.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMod.{0} (@Nat) (@Nat.instMod)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  _v19 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2
  : Nat)))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@instDecidableEqNat (@HMod.hMod.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMod.{0} (@Nat) (@Nat.instMod)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v19 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat)
  (250 : Nat) (@instOfNatNat (250 : Nat))) (@OfNat.ofNat.{0} (@Nat) (304 : Nat) (@instOfNatNat (304 : Nat)))))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12) (@ite.{(0 + 1)} (@Nat) (@LE.le.{0} (@Nat) (@instLENat)
  (@Pnp4.Frontier.ContractExpansion.bitLength _v14) _v19) (@Nat.decLe (@Pnp4.Frontier.ContractExpansion.bitLength _v14)
  _v19) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v13 _v19) _v14) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))) _v25) (fun (_v26 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12))) =>
(@ite.{(0 + 1)} (∀ (_v27 : (@Nat)),
(@Option.{0} (@Bool))) (@LE.le.{0} (@Nat) (@instLENat) (@Pnp4.Frontier.ContractExpansion.bitLength _v14) _v19)
  (@Nat.decLe (@Pnp4.Frontier.ContractExpansion.bitLength _v14) _v19) (@AllArityBitLength.Target.seedImage _v21 _v13 _v19
  _v14) _v21 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12) _v26)))))) (@And (∀ (_v26 : (@Nat)),
(∀ (_v27 : (@LT.lt.{0} (@Nat) (@instLTNat) _v26 _v24)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3) _v12 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3) _v12 _v26 _v22))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0) (@Cursor.q _v0
  (@OfNat.ofNat.{0} (@Nat) (329 : Nat) (@instOfNatNat (329 : Nat)))))))) (@And (∀ (_v26 : (@LT.lt.{0} (@Nat) (@instLTNat)
  _v19 (@Pnp4.Frontier.ContractExpansion.bitLength _v14))),
(@LT.lt.{0} (@Nat) (@instLTNat) _v10 (@Cursor.Target.M _v0 _v14 _v8))) (∀ (_v26 : (@LE.le.{0} (@Nat) (@instLENat)
  (@Pnp4.Frontier.ContractExpansion.bitLength _v14) _v19)),
(∀ (_v27 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0}
  (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12))),
(@Exists.{(0 + 1)} (@Nat) (fun (_v28 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v28 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (1024 : Nat) (@instOfNatNat (1024 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 _v19)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 :
  Nat)))))) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3) _v12)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3) _v12 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v24 _v28) _v22) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight
  (@SmallIngress.producer) (@Cursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3) _v12
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3) _v12 (@Cursor.q _v0 (@ite.{(0 + 1)} (@Nat) (@LE.le.{0}
  (@Nat) (@instLENat) _v14 _v19) (@Nat.decLe _v14 _v19) (@OfNat.ofNat.{0} (@Nat) (411 : Nat) (@instOfNatNat (411 : Nat)))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (798 : Nat)
  (@instOfNatNat (798 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (93 : Nat) (@instOfNatNat (93 : Nat))) _v0)))) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3) _v12) (@ite.{(0 + 1)} (@Nat) (@LE.le.{0} (@Nat)
  (@instLENat) _v14 _v19) (@Nat.decLe _v14 _v19) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0}
  (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v13 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@lt_of_le_of_lt.{0} (@Nat)
  (@Nat.instPreorder) (@ite.{(0 + 1)} (@Nat) (@LE.le.{0} (@Nat) (@instLENat) _v14 _v19) (@Nat.decLe _v14 _v19)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (7 :
  Nat) (@instOfNatNat (7 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3) _v12) (@Decidable.casesOn.{0} (@LE.le.{0} (@Nat)
  (@instLENat) _v14 _v19) (fun (_v29 : (@Decidable (@LE.le.{0} (@Nat) (@instLENat) _v14 _v19))) =>
(@LE.le.{0} (@Nat) (@instLENat) (@ite.{(0 + 1)} (@Nat) (@LE.le.{0} (@Nat) (@instLENat) _v14 _v19) (@Nat.decLe _v14 _v19)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (7 :
  Nat) (@instOfNatNat (7 : Nat)))))) (@Nat.decLe _v14 _v19) (fun (_v29 : (@Not (@LE.le.{0} (@Nat) (@instLENat) _v14
  _v19))) =>
(@Eq.mpr.{0} (@LE.le.{0} (@Nat) (@instLENat) (@ite.{(0 + 1)} (@Nat) (@LE.le.{0} (@Nat) (@instLENat) _v14 _v19)
  (@Nat.decLe _v14 _v19) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v19)) _v14)
  (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))) (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))))
  (@id.{0} (@Eq.{(0 + 1)} (Sort 0) (@LE.le.{0} (@Nat) (@instLENat) (@ite.{(0 + 1)} (@Nat) (@LE.le.{0} (@Nat) (@instLENat)
  _v14 _v19) (@Nat.decLe _v14 _v19) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v19)) _v14)
  (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))) (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 :
  Nat)))))) (@congrArg.{(0 + 1), (0 + 1)} (@Nat) (Sort 0) (@ite.{(0 + 1)} (@Nat) (@LE.le.{0} (@Nat) (@instLENat) _v14
  _v19) (@Nat.decLe _v14 _v19) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (fun (_v30 :
  (@Nat)) =>
(@LE.le.{0} (@Nat) (@instLENat) _v30 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (7 :
  Nat) (@instOfNatNat (7 : Nat)))))) (@if_neg.{(0 + 1)} (@LE.le.{0} (@Nat) (@instLENat) _v14 _v19) (@Nat.decLe _v14 _v19)
  _v29 (@Nat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))))) (@Decidable.byContradiction (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))))
  (@Nat.decLe (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0}
  (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))) (fun (_v30 : (@Not (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 :
  Nat))))))) =>
(@CappedWeight.check_accepted_first_product._proof_2 _v0 _v2 _v3 _v7 _v8 _v29 _v30))))) (fun (_v29 : (@LE.le.{0} (@Nat)
  (@instLENat) _v14 _v19)) =>
(@Eq.mpr.{0} (@LE.le.{0} (@Nat) (@instLENat) (@ite.{(0 + 1)} (@Nat) (@LE.le.{0} (@Nat) (@instLENat) _v14 _v19)
  (@Nat.decLe _v14 _v19) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v19)) _v14)
  (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))) (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat)
  (@instOfNatNat (5 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))) (@id.{0}
  (@Eq.{(0 + 1)} (Sort 0) (@LE.le.{0} (@Nat) (@instLENat) (@ite.{(0 + 1)} (@Nat) (@LE.le.{0} (@Nat) (@instLENat) _v14
  _v19) (@Nat.decLe _v14 _v19) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v19)) _v14)
  (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))) (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat)
  (@instOfNatNat (5 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))))) (@congrArg.{(0
  + 1), (0 + 1)} (@Nat) (Sort 0) (@ite.{(0 + 1)} (@Nat) (@LE.le.{0} (@Nat) (@instLENat) _v14 _v19) (@Nat.decLe _v14 _v19)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))) (fun (_v30 : (@Nat)) =>
(@LE.le.{0} (@Nat) (@instLENat) _v30 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (7 :
  Nat) (@instOfNatNat (7 : Nat)))))) (@if_pos.{(0 + 1)} (@LE.le.{0} (@Nat) (@instLENat) _v14 _v19) (@Nat.decLe _v14 _v19)
  _v29 (@Nat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))))) (@Decidable.byContradiction (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@HMul.hMul.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@HMul.hMul.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 :
  Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))) (@Nat.decLe (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat)
  (@instOfNatNat (5 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))) (fun (_v30 :
  (@Not (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (7 :
  Nat) (@instOfNatNat (7 : Nat))))))) =>
(@CappedWeight.check_accepted_first_product._proof_1 _v0 _v2 _v3 _v7 _v8 _v30)))))) _v27)) (fun (_v29 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3) _v12))) =>
(@CappedWeight.Target.image (@AllArityBitLength.Target.seedImage _v21 _v13 _v19 _v14) _v15 _v14 _v13 _v19
  (@Pnp4.Frontier.ContractExpansion.bitLength _v14) (@ite.{(0 + 1)} (@Nat) (@LE.le.{0} (@Nat) (@instLENat) _v14 _v19)
  (@Nat.decLe _v14 _v19) _v14 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@ite.{(0 + 1)} (@Nat)
  (@LE.le.{0} (@Nat) (@instLENat) _v14 _v19) (@Nat.decLe _v14 _v19) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) _v19) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@ite.{(0 + 1)} (@Nat) (@LE.le.{0} (@Nat)
  (@instLENat) _v14 _v19) (@Nat.decLe _v14 _v19) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v19 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3) _v12) _v29)))))) (@And (@LE.le.{0} (@Nat) (@instLENat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v24 _v28) (@HMul.hMul.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (268435456 : Nat) (@instOfNatNat (268435456
  : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v11
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@And (∀ (_v29 : (@Nat)),
(∀ (_v30 : (@LT.lt.{0} (@Nat) (@instLTNat) _v29 _v28)),
(@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3) _v12
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3) _v12 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v24 _v29) _v22))) (@OfNat.ofNat.{0} (@Nat) (699 : Nat) (@instOfNatNat (699 :
  Nat)))))) (∀ (_v29 : (@LT.lt.{0} (@Nat) (@instLTNat) _v19 _v14)),
(@LT.lt.{0} (@Nat) (@instLTNat) _v10 (@Cursor.Target.M _v0 _v14 _v8))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @CappedWeight.check_accepted_first_product

-- Complete literal proposition for CappedWeight.check_accepted_first_product; original proof reused.
theorem PartACanonical.Surface.m0158 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v0)),
(∀ {_v2 : (@Nat)},
(∀ {_v3 : (@Nat)},
(∀ (_v4 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v2)),
(∀ (_v5 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v3)),
(∀ (_v6 : (@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v2
  _v3 _v4 _v5) (@Bool.true))),
(@Exists.{(0 + 1)} (@Sigma.{0, 0} (@Nat) (fun (_v7 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v7)))) (fun (_v7 : (@Sigma.{0, 0} (@Nat) (fun (_v7 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v7))))) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Sigma.{0, 0} (@Nat) (fun (_v8 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v8))))) (@Pnp4.Frontier.ContractExpansion.contentInput?
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v2 _v3) (@Fin.append.{(0 + 1)} _v2 _v3 (@Bool) _v4 _v5)) (@Option.some.{0} (@Sigma.{0, 0} (@Nat) (fun
  (_v8 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v8)))) _v7)) (@And (@LE.le.{0} (@Nat) (@instLENat)
  (@Pnp3.Models.Partial.tableLen (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v8))) _v7)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v8 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v8))) _v7))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v3)) (@Exists.{(0 + 1)} (@Nat) (fun (_v8 : (@Nat)) =>
(@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v2 _v3) _v8) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v9))) _v7)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v9))) _v7))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2
  _v3)))) (fun (_v9 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v2 _v3) _v8) (@Pnp4.Frontier.ContractExpansion.PrefixInput.n
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v9))) _v7)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v9 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v9))) _v7))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2
  _v3))))) =>
(@And (@Eq.{(0 + 1)} (@Option.{0} (@Nat)) (@Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator.gammaZeros?
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v3) (@Fin.append.{(0 + 1)} _v2 _v3
  (@Bool) _v4 _v5)) (@Option.some.{0} (@Nat) _v8)) (let _v10 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v3);
(let _v11 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3);
(let _v12 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation _v11);
(let _v13 : (@Nat) := (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos _v11);
(let _v14 : (@Nat) := (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v14))) _v7)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v14 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v14))) _v7));
(let _v15 : (@Nat) := (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v10 _v8) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat
  (2 : Nat))));
(let _v16 : (∀ (_v16 : (@Nat)),
(@Option.{0} (@Bool))) := (@Body.extend (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3) _v12
  (@Body.installedTape (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3) _v12 (@SmallIngress.prepared _v2 _v3
  _v12 _v4 _v5 _v8 _v14) _v15 _v14));
(let _v17 : (∀ (_v17 : (@Nat)),
(@Option.{0} (@Bool))) := (@Stream.Target.image _v16 _v10 _v8 _v14 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v8)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v14) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v14) (@Bool.false));
(let _v18 : (@Nat) := (@Min.min.{0} (@Nat) (@Nat.instMin_mathlib) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v8)) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) _v14)) _v10);
(let _v19 : (@Nat) := (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v10 _v18);
(let _v20 : (∀ (_v20 : (@Nat)),
(@Option.{0} (@Bool))) := (@CappedWorkspace.Target.image (@SuffixCap.Target.image _v17 _v13 _v19) _v15 _v14 _v13 _v19);
(let _v21 : (∀ (_v21 : (@Nat)),
(@Option.{0} (@Bool))) := (@RuntimeBitLength.Target.fullImage _v20 _v15 _v14 _v13 _v19);
(let _v22 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3) _v12) :=
  (@Pnp3.Complexity.Uniform.V1.initialConfig (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3) _v12 (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair
  _v2 _v3 _v4 _v5));
(@And (∀ (_v23 : (@Eq.{(0 + 1)} (@Nat) _v18 _v10)),
(@Exists.{(0 + 1)} (@Nat) (fun (_v24 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v24 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (67108864 : Nat) (@instOfNatNat (67108864 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@And (@LE.le.{0} (@Nat) (@instLENat) _v10
  (@Cursor.Target.M _v0 _v14 _v8)) (@And (@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.padRead (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2 _v3) (@Fin.append.{(0 + 1)} _v2 _v3 (@Bool) _v4 _v5)
  (@Cursor.Target.M _v0 _v14 _v8)) (@Bool.false)) (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3) _v12) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3) _v12 _v24 _v22)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@SmallIngress.producer) (@Cursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2
  _v3)) (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2
  _v3)) (@Cursor.mReady _v0 (@Fin.mk (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@of_decide_eq_true (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Nat.decLt
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 :
  Nat)))) (@id.{0} (@Eq.{(0 + 1)} (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Nat.decLt
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 :
  Nat))))) (@Bool.true)) (@Eq.refl.{(0 + 1)} (@Bool) (@Bool.true)))))) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2
  _v3))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v10 _v8) _v14) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v9) (fun (_v25 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2
  _v3))))) =>
(@_v17 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2
  _v3))) _v25)))))))))))) (∀ (_v23 : (@LT.lt.{0} (@Nat) (@instLTNat) _v18 _v10)),
(@Exists.{(0 + 1)} (@Nat) (fun (_v24 : (@Nat)) =>
(@Exists.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@ite.{(0 + 1)} (@Nat) (@LE.le.{0} (@Nat) (@instLENat)
  (@Pnp4.Frontier.ContractExpansion.bitLength _v14) _v19) (@Nat.decLe (@Pnp4.Frontier.ContractExpansion.bitLength _v14)
  _v19) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v13 _v19) _v14) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12)) (fun (_v25 : (@LT.lt.{0} (@Nat) (@instLTNat) (@ite.{(0 + 1)} (@Nat)
  (@LE.le.{0} (@Nat) (@instLENat) (@Pnp4.Frontier.ContractExpansion.bitLength _v14) _v19) (@Nat.decLe
  (@Pnp4.Frontier.ContractExpansion.bitLength _v14) _v19) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0}
  (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 _v19) _v14) (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12))) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v24 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (67108864 : Nat) (@instOfNatNat (67108864 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v11 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))))) (@And (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12)) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3) _v12) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3) _v12 _v24 _v22)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight (@SmallIngress.producer) (@Cursor.machine _v0) _v11 _v12
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0)) _v11
  _v12 (@Cursor.q _v0 (@ite.{(0 + 1)} (@Nat) (@LE.le.{0} (@Nat) (@instLENat) (@Pnp4.Frontier.ContractExpansion.bitLength
  _v14) _v19) (@Nat.decLe (@Pnp4.Frontier.ContractExpansion.bitLength _v14) _v19) (@OfNat.ofNat.{0} (@Nat) (329 : Nat)
  (@instOfNatNat (329 : Nat))) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Nat) (@HMod.hMod.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMod.{0} (@Nat) (@Nat.instMod)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  _v19 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2
  : Nat)))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@instDecidableEqNat (@HMod.hMod.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMod.{0} (@Nat) (@Nat.instMod)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v19 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat)
  (250 : Nat) (@instOfNatNat (250 : Nat))) (@OfNat.ofNat.{0} (@Nat) (304 : Nat) (@instOfNatNat (304 : Nat)))))) (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12) (@ite.{(0 + 1)} (@Nat) (@LE.le.{0} (@Nat) (@instLENat)
  (@Pnp4.Frontier.ContractExpansion.bitLength _v14) _v19) (@Nat.decLe (@Pnp4.Frontier.ContractExpansion.bitLength _v14)
  _v19) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v13 _v19) _v14) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))) _v25) (fun (_v26 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12))) =>
(@ite.{(0 + 1)} (∀ (_v27 : (@Nat)),
(@Option.{0} (@Bool))) (@LE.le.{0} (@Nat) (@instLENat) (@Pnp4.Frontier.ContractExpansion.bitLength _v14) _v19)
  (@Nat.decLe (@Pnp4.Frontier.ContractExpansion.bitLength _v14) _v19) (@AllArityBitLength.Target.seedImage _v21 _v13 _v19
  _v14) _v21 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12) _v26)))))) (@And (∀ (_v26 : (@Nat)),
(∀ (_v27 : (@LT.lt.{0} (@Nat) (@instLTNat) _v26 _v24)),
(@Ne.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3) _v12 (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3) _v12 _v26 _v22))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0) (@Cursor.q _v0
  (@OfNat.ofNat.{0} (@Nat) (329 : Nat) (@instOfNatNat (329 : Nat)))))))) (@And (∀ (_v26 : (@LT.lt.{0} (@Nat) (@instLTNat)
  _v19 (@Pnp4.Frontier.ContractExpansion.bitLength _v14))),
(@LT.lt.{0} (@Nat) (@instLTNat) _v10 (@Cursor.Target.M _v0 _v14 _v8))) (∀ (_v26 : (@LE.le.{0} (@Nat) (@instLENat)
  (@Pnp4.Frontier.ContractExpansion.bitLength _v14) _v19)),
(∀ (_v27 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0}
  (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v11 _v12))),
(@Exists.{(0 + 1)} (@Nat) (fun (_v28 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v28 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (1024 : Nat) (@instOfNatNat (1024 : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v14 _v19)
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 :
  Nat)))))) (@And (@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3) _v12)
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3) _v12 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v24 _v28) _v22) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqEmbedRight
  (@SmallIngress.producer) (@Cursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3) _v12
  (@Pnp3.Complexity.Uniform.V1.Config.mk (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Cursor.machine _v0))
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3) _v12 (@Cursor.q _v0 (@ite.{(0 + 1)} (@Nat) (@LE.le.{0}
  (@Nat) (@instLENat) _v14 _v19) (@Nat.decLe _v14 _v19) (@OfNat.ofNat.{0} (@Nat) (411 : Nat) (@instOfNatNat (411 : Nat)))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (798 : Nat)
  (@instOfNatNat (798 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (93 : Nat) (@instOfNatNat (93 : Nat))) _v0)))) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3) _v12) (@ite.{(0 + 1)} (@Nat) (@LE.le.{0} (@Nat)
  (@instLENat) _v14 _v19) (@Nat.decLe _v14 _v19) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0}
  (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v13 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@lt_of_le_of_lt.{0} (@Nat)
  (@Nat.instPreorder) (@ite.{(0 + 1)} (@Nat) (@LE.le.{0} (@Nat) (@instLENat) _v14 _v19) (@Nat.decLe _v14 _v19)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (7 :
  Nat) (@instOfNatNat (7 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3) _v12) (@Decidable.casesOn.{0} (@LE.le.{0} (@Nat)
  (@instLENat) _v14 _v19) (fun (_v29 : (@Decidable (@LE.le.{0} (@Nat) (@instLENat) _v14 _v19))) =>
(@LE.le.{0} (@Nat) (@instLENat) (@ite.{(0 + 1)} (@Nat) (@LE.le.{0} (@Nat) (@instLENat) _v14 _v19) (@Nat.decLe _v14 _v19)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (7 :
  Nat) (@instOfNatNat (7 : Nat)))))) (@Nat.decLe _v14 _v19) (fun (_v29 : (@Not (@LE.le.{0} (@Nat) (@instLENat) _v14
  _v19))) =>
(@Eq.mpr.{0} (@LE.le.{0} (@Nat) (@instLENat) (@ite.{(0 + 1)} (@Nat) (@LE.le.{0} (@Nat) (@instLENat) _v14 _v19)
  (@Nat.decLe _v14 _v19) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v19)) _v14)
  (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))) (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))))
  (@id.{0} (@Eq.{(0 + 1)} (Sort 0) (@LE.le.{0} (@Nat) (@instLENat) (@ite.{(0 + 1)} (@Nat) (@LE.le.{0} (@Nat) (@instLENat)
  _v14 _v19) (@Nat.decLe _v14 _v19) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v19)) _v14)
  (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))) (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 :
  Nat)))))) (@congrArg.{(0 + 1), (0 + 1)} (@Nat) (Sort 0) (@ite.{(0 + 1)} (@Nat) (@LE.le.{0} (@Nat) (@instLENat) _v14
  _v19) (@Nat.decLe _v14 _v19) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (fun (_v30 :
  (@Nat)) =>
(@LE.le.{0} (@Nat) (@instLENat) _v30 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (7 :
  Nat) (@instOfNatNat (7 : Nat)))))) (@if_neg.{(0 + 1)} (@LE.le.{0} (@Nat) (@instLENat) _v14 _v19) (@Nat.decLe _v14 _v19)
  _v29 (@Nat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))))) (@Decidable.byContradiction (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))))
  (@Nat.decLe (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0}
  (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))) (fun (_v30 : (@Not (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 :
  Nat))))))) =>
(@CappedWeight.check_accepted_first_product._proof_2 _v0 _v2 _v3 _v7 _v8 _v29 _v30))))) (fun (_v29 : (@LE.le.{0} (@Nat)
  (@instLENat) _v14 _v19)) =>
(@Eq.mpr.{0} (@LE.le.{0} (@Nat) (@instLENat) (@ite.{(0 + 1)} (@Nat) (@LE.le.{0} (@Nat) (@instLENat) _v14 _v19)
  (@Nat.decLe _v14 _v19) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v19)) _v14)
  (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))) (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat)
  (@instOfNatNat (5 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))) (@id.{0}
  (@Eq.{(0 + 1)} (Sort 0) (@LE.le.{0} (@Nat) (@instLENat) (@ite.{(0 + 1)} (@Nat) (@LE.le.{0} (@Nat) (@instLENat) _v14
  _v19) (@Nat.decLe _v14 _v19) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v19)) _v14)
  (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))) (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat)
  (@instOfNatNat (5 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))))) (@congrArg.{(0
  + 1), (0 + 1)} (@Nat) (Sort 0) (@ite.{(0 + 1)} (@Nat) (@LE.le.{0} (@Nat) (@instLENat) _v14 _v19) (@Nat.decLe _v14 _v19)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))) (fun (_v30 : (@Nat)) =>
(@LE.le.{0} (@Nat) (@instLENat) _v30 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (7 :
  Nat) (@instOfNatNat (7 : Nat)))))) (@if_pos.{(0 + 1)} (@LE.le.{0} (@Nat) (@instLENat) _v14 _v19) (@Nat.decLe _v14 _v19)
  _v29 (@Nat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))))) (@Decidable.byContradiction (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@HMul.hMul.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@HMul.hMul.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 :
  Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))) (@Nat.decLe (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat)
  (@instOfNatNat (5 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat))))) (fun (_v30 :
  (@Not (@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v13 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (5 : Nat) (@instOfNatNat (5 : Nat))) _v19)) _v14) (@OfNat.ofNat.{0} (@Nat) (7 :
  Nat) (@instOfNatNat (7 : Nat))))))) =>
(@CappedWeight.check_accepted_first_product._proof_1 _v0 _v2 _v3 _v7 _v8 _v30)))))) _v27)) (fun (_v29 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3) _v12))) =>
(@CappedWeight.Target.image (@AllArityBitLength.Target.seedImage _v21 _v13 _v19 _v14) _v15 _v14 _v13 _v19
  (@Pnp4.Frontier.ContractExpansion.bitLength _v14) (@ite.{(0 + 1)} (@Nat) (@LE.le.{0} (@Nat) (@instLENat) _v14 _v19)
  (@Nat.decLe _v14 _v19) _v14 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))) (@ite.{(0 + 1)} (@Nat)
  (@LE.le.{0} (@Nat) (@instLENat) _v14 _v19) (@Nat.decLe _v14 _v19) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat))) _v19) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) (@ite.{(0 + 1)} (@Nat) (@LE.le.{0} (@Nat)
  (@instLENat) _v14 _v19) (@Nat.decLe _v14 _v19) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v19 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3) _v12) _v29)))))) (@And (@LE.le.{0} (@Nat) (@instLENat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v24 _v28) (@HMul.hMul.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (268435456 : Nat) (@instOfNatNat (268435456
  : Nat))) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat)
  (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v11
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 :
  Nat)))))) (@And (∀ (_v29 : (@Nat)),
(∀ (_v30 : (@LT.lt.{0} (@Nat) (@instLTNat) _v29 _v28)),
(@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3) _v12
  (@Pnp3.Complexity.Uniform.V1.UniformTM.run (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v2 _v3) _v12 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v24 _v29) _v22))) (@OfNat.ofNat.{0} (@Nat) (699 : Nat) (@instOfNatNat (699 :
  Nat)))))) (∀ (_v29 : (@LT.lt.{0} (@Nat) (@instLTNat) _v19 _v14)),
(@LT.lt.{0} (@Nat) (@instLTNat) _v10 (@Cursor.Target.M _v0 _v14 _v8))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  exact @CappedWeight.check_accepted_first_product

-- Independent literal expected type for CappedWeight.check_canonical_outcome.
noncomputable def PartACanonical.Types.p0253 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v0)),
(∀ (_v2 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(∀ (_v3 : (@Bool)),
(let _v4 : (@Pnp4.Frontier.TreeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) :=
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0));
(let _v5 : (@Nat) := (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly
  _v0) _v4 (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v2));
(let _v6 : (@Nat) := (@Pnp3.ComplexityInterfaces.certificateLength _v5 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat))));
(let _v7 : (@Pnp4.Frontier.ContractExpansion.PrefixBitVec (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v4 (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat))) _v2))) := (@Pnp4.Frontier.ContractExpansion.zeroPrefixQueryValue
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v4 (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat))) _v2) (fun (_v7 : (@Fin (@Pnp3.Models.Partial.tableLen (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))) _v2)))) =>
_v3));
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v6) (fun (_v8 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v6))
  =>
(@And (@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v5 _v6
  _v7 _v8) (@Bool.true)) (@Exists.{(0 + 1)} (@Nat) (fun (_v9 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v9 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (268435456 : Nat) (@instOfNatNat (268435456 : Nat))) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v5
  _v6) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4
  : Nat)))))) (let _v10 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v4 (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v2)) _v6)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v5
  _v6))) := (@Pnp3.Complexity.Uniform.V1.initialConfig (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v4 (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat))) _v2)) _v6) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v5 _v6)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v4 (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v2)) _v6 _v7 _v8));
(@Or (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v4 (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat))) _v2)) _v6) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v5 _v6)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v4 (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v2)) _v6)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v5
  _v6)) _v9 _v10)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0)
  (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (411 : Nat) (@instOfNatNat (411 : Nat)))))) (@Or (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v4 (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat))) _v2)) _v6) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v5 _v6)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v4 (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v2)) _v6)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v5
  _v6)) _v9 _v10)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0)
  (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat)
  (798 : Nat) (@instOfNatNat (798 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (93 : Nat) (@instOfNatNat (93 : Nat))) _v0))))) (@Or (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v4 (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat))) _v2)) _v6) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v5 _v6)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v4 (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v2)) _v6)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v5
  _v6)) _v9 _v10)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0)
  (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (250 : Nat) (@instOfNatNat (250 : Nat)))))) (@Or (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v4 (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat))) _v2)) _v6) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v5 _v6)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v4 (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v2)) _v6)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v5
  _v6)) _v9 _v10)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0)
  (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (304 : Nat) (@instOfNatNat (304 : Nat)))))) (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v4 (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat))) _v2)) _v6) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v5 _v6)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v4 (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v2)) _v6)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v5
  _v6)) _v9 _v10)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0)
  (@Cursor.mReady _v0 (@Fin.mk (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))) (@of_decide_eq_true (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@id.{0}
  (@Eq.{(0 + 1)} (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))))
  (@Bool.true)) (@Eq.refl.{(0 + 1)} (@Bool) (@Bool.true))))))))))))))))))))))))))) := by
  exact @CappedWeight.check_canonical_outcome

-- Complete literal proposition for CappedWeight.check_canonical_outcome; original proof reused.
theorem PartACanonical.Surface.m0159 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v0)),
(∀ (_v2 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(∀ (_v3 : (@Bool)),
(let _v4 : (@Pnp4.Frontier.TreeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) :=
  (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0));
(let _v5 : (@Nat) := (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly
  _v0) _v4 (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v2));
(let _v6 : (@Nat) := (@Pnp3.ComplexityInterfaces.certificateLength _v5 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat))));
(let _v7 : (@Pnp4.Frontier.ContractExpansion.PrefixBitVec (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v4 (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat))) _v2))) := (@Pnp4.Frontier.ContractExpansion.zeroPrefixQueryValue
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v4 (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat))) _v2) (fun (_v7 : (@Fin (@Pnp3.Models.Partial.tableLen (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat)
  (@instOfNatNat (3 : Nat))) _v2)))) =>
_v3));
(@Exists.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Bitstring _v6) (fun (_v8 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v6))
  =>
(@And (@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation _v0 _v5 _v6
  _v7 _v8) (@Bool.true)) (@Exists.{(0 + 1)} (@Nat) (fun (_v9 : (@Nat)) =>
(@And (@LE.le.{0} (@Nat) (@instLENat) _v9 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (268435456 : Nat) (@instOfNatNat (268435456 : Nat))) (@HPow.hPow.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v5
  _v6) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4
  : Nat)))))) (let _v10 : (@Pnp3.Complexity.Uniform.V1.Config (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@AllArityCursor.machine _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v4 (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v2)) _v6)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v5
  _v6))) := (@Pnp3.Complexity.Uniform.V1.initialConfig (@AllArityCursor.machine _v0)
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v4 (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat))) _v2)) _v6) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v5 _v6)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v4 (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v2)) _v6 _v7 _v8));
(@Or (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v4 (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat))) _v2)) _v6) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v5 _v6)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v4 (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v2)) _v6)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v5
  _v6)) _v9 _v10)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0)
  (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (411 : Nat) (@instOfNatNat (411 : Nat)))))) (@Or (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v4 (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat))) _v2)) _v6) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v5 _v6)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v4 (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v2)) _v6)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v5
  _v6)) _v9 _v10)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0)
  (@Cursor.q _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat)
  (798 : Nat) (@instOfNatNat (798 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (93 : Nat) (@instOfNatNat (93 : Nat))) _v0))))) (@Or (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v4 (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat))) _v2)) _v6) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v5 _v6)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v4 (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v2)) _v6)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v5
  _v6)) _v9 _v10)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0)
  (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (250 : Nat) (@instOfNatNat (250 : Nat)))))) (@Or (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v4 (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat))) _v2)) _v6) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v5 _v6)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v4 (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v2)) _v6)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v5
  _v6)) _v9 _v10)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0)
  (@Cursor.q _v0 (@OfNat.ofNat.{0} (@Nat) (304 : Nat) (@instOfNatNat (304 : Nat)))))) (@Eq.{(0 + 1)} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine _v0)))
  (@Pnp3.Complexity.Uniform.V1.Config.state (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@AllArityCursor.machine
  _v0)) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v4 (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3
  : Nat))) _v2)) _v6) (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation
  (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v5 _v6)) (@Pnp3.Complexity.Uniform.V1.UniformTM.run
  (@AllArityCursor.machine _v0) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength
  (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) _v4 (@Fin.val
  (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v2)) _v6)
  (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v5
  _v6)) _v9 _v10)) (@Pnp3.Complexity.Uniform.V1.UniformTM.seqRight (@SmallIngress.producer) (@Cursor.machine _v0)
  (@Cursor.mReady _v0 (@Fin.mk (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) (@OfNat.ofNat.{0} (@Nat) (2 :
  Nat) (@instOfNatNat (2 : Nat))) (@of_decide_eq_true (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@id.{0}
  (@Eq.{(0 + 1)} (@Bool) (@Decidable.decide (@LT.lt.{0} (@Nat) (@instLTNat) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Nat.decLt (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))))
  (@Bool.true)) (@Eq.refl.{(0 + 1)} (@Bool) (@Bool.true))))))))))))))))))))))))))) := by
  exact @CappedWeight.check_canonical_outcome

-- Independent literal expected type for CappedWeight.check_first_product.
noncomputable def PartACanonical.Types.p0254 :
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
  (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Decidable.byContradiction (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v7)) _v4) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v7)) _v4)
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (fun
  (_v24 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v7)) _v4) (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)))) =>
(@CappedWeight.check_first_product._proof_1 _v0 _v1 _v2 _v3 _v4 _v5 _v6 _v7 _v10 _v22 _v24)))) (fun (_v24 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))) =>
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
  Nat))))) (@Decidable.casesOn.{0} (@LE.le.{0} (@Nat) (@instLENat) _v4 _v7) (fun (_v24 : (@Decidable (@LE.le.{0} (@Nat)
  (@instLENat) _v4 _v7))) =>
(@LT.lt.{0} (@Nat) (@instLTNat) (@ite.{(0 + 1)} (@Nat) (@LE.le.{0} (@Nat) (@instLENat) _v4 _v7) (@Nat.decLe _v4 _v7)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v6 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v7)) _v4) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))) (@Nat.decLe _v4 _v7) (fun (_v24 : (@Not
  (@LE.le.{0} (@Nat) (@instLENat) _v4 _v7))) =>
(@Eq.mpr.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@ite.{(0 + 1)} (@Nat) (@LE.le.{0} (@Nat) (@instLENat) _v4 _v7) (@Nat.decLe
  _v4 _v7) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v6 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v7)) _v4) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (@id.{0} (@Eq.{(0 + 1)} (Sort 0)
  (@LT.lt.{0} (@Nat) (@instLTNat) (@ite.{(0 + 1)} (@Nat) (@LE.le.{0} (@Nat) (@instLENat) _v4 _v7) (@Nat.decLe _v4 _v7)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v6 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v7)) _v4) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))) (@congrArg.{(0 + 1), (0 + 1)} (@Nat)
  (Sort 0) (@ite.{(0 + 1)} (@Nat) (@LE.le.{0} (@Nat) (@instLENat) _v4 _v7) (@Nat.decLe _v4 _v7) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v7)) _v4) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1
  : Nat) (@instOfNatNat (1 : Nat)))) (fun (_v25 : (@Nat)) =>
(@LT.lt.{0} (@Nat) (@instLTNat) _v25 (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))) (@if_neg.{(0 + 1)} (@LE.le.{0}
  (@Nat) (@instLENat) _v4 _v7) (@Nat.decLe _v4 _v7) _v24 (@Nat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v7)) _v4)
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))) (@Decidable.byContradiction
  (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))
  (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat)
  (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (fun (_v25 : (@Not (@LT.lt.{0}
  (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)))) =>
(@CappedWeight.check_first_product._proof_3 _v0 _v1 _v2 _v3 _v4 _v5 _v6 _v7 _v10 _v22 _v24 _v25))))) (fun (_v24 :
  (@LE.le.{0} (@Nat) (@instLENat) _v4 _v7)) =>
(@Eq.mpr.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@ite.{(0 + 1)} (@Nat) (@LE.le.{0} (@Nat) (@instLENat) _v4 _v7) (@Nat.decLe
  _v4 _v7) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v6 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v7)) _v4) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v6 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v7)) _v4) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (@id.{0} (@Eq.{(0 + 1)} (Sort 0) (@LT.lt.{0} (@Nat) (@instLTNat)
  (@ite.{(0 + 1)} (@Nat) (@LE.le.{0} (@Nat) (@instLENat) _v4 _v7) (@Nat.decLe _v4 _v7) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v7)) _v4) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v7)) _v4) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1
  _v2))) (@congrArg.{(0 + 1), (0 + 1)} (@Nat) (Sort 0) (@ite.{(0 + 1)} (@Nat) (@LE.le.{0} (@Nat) (@instLENat) _v4 _v7)
  (@Nat.decLe _v4 _v7) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v6 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v7)) _v4) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v7)) _v4)
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (fun (_v25 : (@Nat)) =>
(@LT.lt.{0} (@Nat) (@instLTNat) _v25 (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))) (@if_pos.{(0 + 1)} (@LE.le.{0}
  (@Nat) (@instLENat) _v4 _v7) (@Nat.decLe _v4 _v7) _v24 (@Nat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v7)) _v4)
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))) (@Decidable.byContradiction
  (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v7)) _v4) (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (@Nat.decLt (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v7)) _v4) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (fun (_v25 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v7)) _v4) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)))) =>
(@CappedWeight.check_first_product._proof_2 _v0 _v1 _v2 _v3 _v4 _v5 _v6 _v7 _v22 _v24 _v25))))))) (fun (_v24 : (@Fin
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
  (@Decidable.byContradiction (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v7)) _v4)
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))
  (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v6 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v7)) _v4) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (fun (_v26 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v7)) _v4) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)))) =>
(@CappedWeight.check_first_product._proof_1 _v0 _v1 _v2 _v3 _v4 _v5 _v6 _v7 _v10 _v22 _v26)))) (fun (_v26 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))) =>
(@_v8 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) _v26))))))) (@OfNat.ofNat.{0} (@Nat) (411 : Nat)
  (@instOfNatNat (411 : Nat))))))))))))))))))))))))))))))))) := by
  exact @CappedWeight.check_first_product

-- Complete literal proposition for CappedWeight.check_first_product; original proof reused.
theorem PartACanonical.Surface.m0160 :
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
  (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Decidable.byContradiction (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v7)) _v4) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v7)) _v4)
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (fun
  (_v24 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v7)) _v4) (@OfNat.ofNat.{0} (@Nat)
  (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)))) =>
(@CappedWeight.check_first_product._proof_1 _v0 _v1 _v2 _v3 _v4 _v5 _v6 _v7 _v10 _v22 _v24)))) (fun (_v24 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))) =>
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
  Nat))))) (@Decidable.casesOn.{0} (@LE.le.{0} (@Nat) (@instLENat) _v4 _v7) (fun (_v24 : (@Decidable (@LE.le.{0} (@Nat)
  (@instLENat) _v4 _v7))) =>
(@LT.lt.{0} (@Nat) (@instLTNat) (@ite.{(0 + 1)} (@Nat) (@LE.le.{0} (@Nat) (@instLENat) _v4 _v7) (@Nat.decLe _v4 _v7)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v6 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v7)) _v4) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))) (@Nat.decLe _v4 _v7) (fun (_v24 : (@Not
  (@LE.le.{0} (@Nat) (@instLENat) _v4 _v7))) =>
(@Eq.mpr.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@ite.{(0 + 1)} (@Nat) (@LE.le.{0} (@Nat) (@instLENat) _v4 _v7) (@Nat.decLe
  _v4 _v7) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v6 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v7)) _v4) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (@id.{0} (@Eq.{(0 + 1)} (Sort 0)
  (@LT.lt.{0} (@Nat) (@instLTNat) (@ite.{(0 + 1)} (@Nat) (@LE.le.{0} (@Nat) (@instLENat) _v4 _v7) (@Nat.decLe _v4 _v7)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v6 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v7)) _v4) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))) (@congrArg.{(0 + 1), (0 + 1)} (@Nat)
  (Sort 0) (@ite.{(0 + 1)} (@Nat) (@LE.le.{0} (@Nat) (@instLENat) _v4 _v7) (@Nat.decLe _v4 _v7) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v7)) _v4) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1
  : Nat) (@instOfNatNat (1 : Nat)))) (fun (_v25 : (@Nat)) =>
(@LT.lt.{0} (@Nat) (@instLTNat) _v25 (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))) (@if_neg.{(0 + 1)} (@LE.le.{0}
  (@Nat) (@instLENat) _v4 _v7) (@Nat.decLe _v4 _v7) _v24 (@Nat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v7)) _v4)
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))) (@Decidable.byContradiction
  (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))
  (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat)
  (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (fun (_v25 : (@Not (@LT.lt.{0}
  (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)))) =>
(@CappedWeight.check_first_product._proof_3 _v0 _v1 _v2 _v3 _v4 _v5 _v6 _v7 _v10 _v22 _v24 _v25))))) (fun (_v24 :
  (@LE.le.{0} (@Nat) (@instLENat) _v4 _v7)) =>
(@Eq.mpr.{0} (@LT.lt.{0} (@Nat) (@instLTNat) (@ite.{(0 + 1)} (@Nat) (@LE.le.{0} (@Nat) (@instLENat) _v4 _v7) (@Nat.decLe
  _v4 _v7) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v6 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v7)) _v4) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (@LT.lt.{0} (@Nat) (@instLTNat)
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v6 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v7)) _v4) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (@id.{0} (@Eq.{(0 + 1)} (Sort 0) (@LT.lt.{0} (@Nat) (@instLTNat)
  (@ite.{(0 + 1)} (@Nat) (@LE.le.{0} (@Nat) (@instLENat) _v4 _v7) (@Nat.decLe _v4 _v7) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v7)) _v4) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@HMul.hMul.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v7)) _v4) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1
  _v2))) (@congrArg.{(0 + 1), (0 + 1)} (@Nat) (Sort 0) (@ite.{(0 + 1)} (@Nat) (@LE.le.{0} (@Nat) (@instLENat) _v4 _v7)
  (@Nat.decLe _v4 _v7) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v6 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat))
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v7)) _v4) (@OfNat.ofNat.{0} (@Nat) (4 : Nat)
  (@instOfNatNat (4 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v7)) _v4)
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (fun (_v25 : (@Nat)) =>
(@LT.lt.{0} (@Nat) (@instLTNat) _v25 (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))) (@if_pos.{(0 + 1)} (@LE.le.{0}
  (@Nat) (@instLENat) _v4 _v7) (@Nat.decLe _v4 _v7) _v24 (@Nat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v7)) _v4)
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v6 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))) (@Decidable.byContradiction
  (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v7)) _v4) (@OfNat.ofNat.{0} (@Nat) (4 :
  Nat) (@instOfNatNat (4 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (@Nat.decLt (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v7)) _v4) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (fun (_v25 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v7)) _v4) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)))) =>
(@CappedWeight.check_first_product._proof_2 _v0 _v1 _v2 _v3 _v4 _v5 _v6 _v7 _v22 _v24 _v25))))))) (fun (_v24 : (@Fin
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
  (@Decidable.byContradiction (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v7)) _v4)
  (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat)))) (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))
  (@Nat.decLt (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v6 (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v7)) _v4) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)) (fun (_v26 : (@Not (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v6
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v7)) _v4) (@OfNat.ofNat.{0} (@Nat) (4 : Nat) (@instOfNatNat (4 : Nat))))
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2)))) =>
(@CappedWeight.check_first_product._proof_1 _v0 _v1 _v2 _v3 _v4 _v5 _v6 _v7 _v10 _v22 _v26)))) (fun (_v26 : (@Fin
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2))) =>
(@_v8 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v1 _v2) _v26))))))) (@OfNat.ofNat.{0} (@Nat) (411 : Nat)
  (@instOfNatNat (411 : Nat))))))))))))))))))))))))))))))))) := by
  exact @CappedWeight.check_first_product

-- Independent literal expected type for CappedWeight.check_instructions_equation.
noncomputable def PartACanonical.Types.p0255 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@List.{0} (@Nat)) (@CappedWeight.instructions _v0) (let _v1 : (@List.{0} (@Nat)) := (let _v1 :
  (@List.{0} (@Nat)) := (let _v1 : (@List.{0} (@Nat)) := (let _v1 : (@List.{0} (@Nat)) := (let _v1 : (@List.{0} (@Nat)) :=
  (let _v1 : (@List.{0} (@Nat)) := (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3696 : Nat) (@instOfNatNat (3696 :
  Nat))) (@List.cons.{0} (@Nat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (7183 : Nat) (@instOfNatNat (7183 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (837 : Nat) (@instOfNatNat (837 : Nat))) _v0))
  (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3693 : Nat) (@instOfNatNat (3693 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3696 : Nat) (@instOfNatNat (3696 : Nat))) (@List.nil.{0} (@Nat))))));
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
  (3358 : Nat) (@instOfNatNat (3358 : Nat))) _v4)))))))))));
(let _v2 : (@List.{0} (@Nat)) := (let _v2 : (@List.{0} (@Nat)) := (let _v2 : (@List.{0} (@Nat)) := (let _v2 : (@List.{0}
  (@Nat)) := (let _v2 : (@List.{0} (@Nat)) := (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3327 : Nat) (@instOfNatNat
  (3327 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (361 : Nat) (@instOfNatNat (361 : Nat))) (@List.cons.{0}
  (@Nat) (@OfNat.ofNat.{0} (@Nat) (3333 : Nat) (@instOfNatNat (3333 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0}
  (@Nat) (367 : Nat) (@instOfNatNat (367 : Nat))) _v1))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3306 : Nat) (@instOfNatNat (3306 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3309 : Nat) (@instOfNatNat (3309 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3321 : Nat) (@instOfNatNat (3321 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3324 : Nat) (@instOfNatNat
  (3324 : Nat))) _v2)))));
(let _v3 : (@List.{0} (@Nat)) := (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3303 : Nat) (@instOfNatNat (3303 :
  Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3306 : Nat) (@instOfNatNat (3306 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3309 : Nat) (@instOfNatNat (3309 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3313 : Nat) (@instOfNatNat (3313 : Nat))) _v2))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3291 : Nat) (@instOfNatNat (3291 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3295 : Nat) (@instOfNatNat (3295 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3288 : Nat) (@instOfNatNat (3288 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3291 : Nat) (@instOfNatNat
  (3291 : Nat))) _v3))))));
(let _v3 : (@List.{0} (@Nat)) := (let _v3 : (@List.{0} (@Nat)) := (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3270
  : Nat) (@instOfNatNat (3270 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3273 : Nat) (@instOfNatNat (3273 :
  Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3285 : Nat) (@instOfNatNat (3285 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3288 : Nat) (@instOfNatNat (3288 : Nat))) _v2))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3267 : Nat) (@instOfNatNat (3267 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3270 : Nat) (@instOfNatNat (3270 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3273 : Nat) (@instOfNatNat (3273 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3277 : Nat) (@instOfNatNat
  (3277 : Nat))) _v3)))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3237 : Nat) (@instOfNatNat (3237 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3249 : Nat) (@instOfNatNat (3249 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3252 : Nat) (@instOfNatNat (3252 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3255 : Nat) (@instOfNatNat
  (3255 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3259 : Nat) (@instOfNatNat (3259 : Nat)))
  (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3252 : Nat) (@instOfNatNat (3252 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3255 : Nat) (@instOfNatNat (3255 : Nat))) _v3)))))))));
(let _v3 : (@List.{0} (@Nat)) := (let _v3 : (@List.{0} (@Nat)) := (let _v3 : (@List.{0} (@Nat)) := (@List.cons.{0}
  (@Nat) (@OfNat.ofNat.{0} (@Nat) (3225 : Nat) (@instOfNatNat (3225 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0}
  (@Nat) (3228 : Nat) (@instOfNatNat (3228 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3628 : Nat)
  (@instOfNatNat (3628 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3234 : Nat) (@instOfNatNat (3234 : Nat)))
  _v2))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3231 : Nat) (@instOfNatNat (3231 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3228 : Nat) (@instOfNatNat (3228 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3221 : Nat) (@instOfNatNat (3221 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3241 : Nat) (@instOfNatNat
  (3241 : Nat))) _v3)))));
(let _v4 : (@List.{0} (@Nat)) := (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3203 : Nat) (@instOfNatNat (3203 :
  Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3215 : Nat) (@instOfNatNat (3215 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3218 : Nat) (@instOfNatNat (3218 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3221 : Nat) (@instOfNatNat (3221 : Nat))) _v3))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3200 : Nat) (@instOfNatNat (3200 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3203 : Nat) (@instOfNatNat (3203 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3205 : Nat) (@instOfNatNat (3205 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3200 : Nat) (@instOfNatNat
  (3200 : Nat))) _v4))))));
(let _v4 : (@List.{0} (@Nat)) := (let _v4 : (@List.{0} (@Nat)) := (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3187
  : Nat) (@instOfNatNat (3187 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3182 : Nat) (@instOfNatNat (3182 :
  Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3185 : Nat) (@instOfNatNat (3185 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3197 : Nat) (@instOfNatNat (3197 : Nat))) _v3))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3167 : Nat) (@instOfNatNat (3167 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3179 : Nat) (@instOfNatNat (3179 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3182 : Nat) (@instOfNatNat (3182 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3185 : Nat) (@instOfNatNat
  (3185 : Nat))) _v4)))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3146 : Nat) (@instOfNatNat (3146 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3149 : Nat) (@instOfNatNat (3149 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3161 : Nat) (@instOfNatNat (3161 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3164 : Nat) (@instOfNatNat
  (3164 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3167 : Nat) (@instOfNatNat (3167 : Nat)))
  (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3169 : Nat) (@instOfNatNat (3169 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3164 : Nat) (@instOfNatNat (3164 : Nat))) _v4))))))))));
(let _v3 : (@List.{0} (@Nat)) := (let _v3 : (@List.{0} (@Nat)) := (let _v3 : (@List.{0} (@Nat)) := (let _v3 : (@List.{0}
  (@Nat)) := (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3143 : Nat) (@instOfNatNat (3143 : Nat))) (@List.cons.{0}
  (@Nat) (@OfNat.ofNat.{0} (@Nat) (3146 : Nat) (@instOfNatNat (3146 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0}
  (@Nat) (3149 : Nat) (@instOfNatNat (3149 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3151 : Nat)
  (@instOfNatNat (3151 : Nat))) _v2))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3131 : Nat) (@instOfNatNat (3131 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3125 : Nat) (@instOfNatNat (3125 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3137 : Nat) (@instOfNatNat (3137 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3131 : Nat) (@instOfNatNat
  (3131 : Nat))) _v3)))));
(let _v4 : (@List.{0} (@Nat)) := (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3110 : Nat) (@instOfNatNat (3110 :
  Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3113 : Nat) (@instOfNatNat (3113 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3125 : Nat) (@instOfNatNat (3125 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3128 : Nat) (@instOfNatNat (3128 : Nat))) _v3))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3350 : Nat) (@instOfNatNat (3350 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3113 : Nat) (@instOfNatNat (3113 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3102 : Nat) (@instOfNatNat (3102 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3115 : Nat) (@instOfNatNat
  (3115 : Nat))) _v4))))));
(let _v4 : (@List.{0} (@Nat)) := (let _v4 : (@List.{0} (@Nat)) := (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3084
  : Nat) (@instOfNatNat (3084 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3096 : Nat) (@instOfNatNat (3096 :
  Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3099 : Nat) (@instOfNatNat (3099 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3102 : Nat) (@instOfNatNat (3102 : Nat))) _v3))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (364 : Nat) (@instOfNatNat (364 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3084 : Nat) (@instOfNatNat (3084 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3088 : Nat) (@instOfNatNat (3088 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (364 : Nat) (@instOfNatNat
  (364 : Nat))) _v4)))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3060 : Nat) (@instOfNatNat (3060 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3063 : Nat) (@instOfNatNat (3063 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3066 : Nat) (@instOfNatNat (3066 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (361 : Nat) (@instOfNatNat
  (361 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3072 : Nat) (@instOfNatNat (3072 : Nat))) (@List.cons.{0}
  (@Nat) (@OfNat.ofNat.{0} (@Nat) (367 : Nat) (@instOfNatNat (367 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3069 : Nat) (@instOfNatNat (3069 : Nat))) _v4)))))))));
(let _v4 : (@List.{0} (@Nat)) := (let _v4 : (@List.{0} (@Nat)) := (let _v4 : (@List.{0} (@Nat)) := (@List.cons.{0}
  (@Nat) (@OfNat.ofNat.{0} (@Nat) (3048 : Nat) (@instOfNatNat (3048 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0}
  (@Nat) (3052 : Nat) (@instOfNatNat (3052 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3045 : Nat)
  (@instOfNatNat (3045 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3048 : Nat) (@instOfNatNat (3048 : Nat)))
  _v3))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3027 : Nat) (@instOfNatNat (3027 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3030 : Nat) (@instOfNatNat (3030 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3042 : Nat) (@instOfNatNat (3042 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3045 : Nat) (@instOfNatNat
  (3045 : Nat))) _v4)))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3016 : Nat) (@instOfNatNat (3016 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3009 : Nat) (@instOfNatNat (3009 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3012 : Nat) (@instOfNatNat (3012 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3024 : Nat) (@instOfNatNat
  (3024 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3027 : Nat) (@instOfNatNat (3027 : Nat)))
  (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3030 : Nat) (@instOfNatNat (3030 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3034 : Nat) (@instOfNatNat (3034 : Nat))) _v4))))))));
(let _v5 : (@List.{0} (@Nat)) := (let _v5 : (@List.{0} (@Nat)) := (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (2994
  : Nat) (@instOfNatNat (2994 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3006 : Nat) (@instOfNatNat (3006 :
  Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3009 : Nat) (@instOfNatNat (3009 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3012 : Nat) (@instOfNatNat (3012 : Nat))) _v4))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (364 : Nat) (@instOfNatNat (364 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (2991 : Nat) (@instOfNatNat (2991 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (2998 : Nat) (@instOfNatNat (2998 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (2991 : Nat) (@instOfNatNat
  (2991 : Nat))) _v5)))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (2972 : Nat) (@instOfNatNat (2972 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (2975 : Nat) (@instOfNatNat (2975 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (2978 : Nat) (@instOfNatNat (2978 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (2979 : Nat) (@instOfNatNat
  (2979 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (2982 : Nat) (@instOfNatNat (2982 : Nat)))
  (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (2978 : Nat) (@instOfNatNat (2978 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3430 : Nat) (@instOfNatNat (3430 : Nat))) _v5)))))))))))))) := by
  exact @CappedWeight.check_instructions_equation

-- Complete literal proposition for CappedWeight.check_instructions_equation; original proof reused.
theorem PartACanonical.Surface.m0161 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@List.{0} (@Nat)) (@CappedWeight.instructions _v0) (let _v1 : (@List.{0} (@Nat)) := (let _v1 :
  (@List.{0} (@Nat)) := (let _v1 : (@List.{0} (@Nat)) := (let _v1 : (@List.{0} (@Nat)) := (let _v1 : (@List.{0} (@Nat)) :=
  (let _v1 : (@List.{0} (@Nat)) := (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3696 : Nat) (@instOfNatNat (3696 :
  Nat))) (@List.cons.{0} (@Nat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@OfNat.ofNat.{0} (@Nat) (7183 : Nat) (@instOfNatNat (7183 : Nat))) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (837 : Nat) (@instOfNatNat (837 : Nat))) _v0))
  (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3693 : Nat) (@instOfNatNat (3693 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3696 : Nat) (@instOfNatNat (3696 : Nat))) (@List.nil.{0} (@Nat))))));
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
  (3358 : Nat) (@instOfNatNat (3358 : Nat))) _v4)))))))))));
(let _v2 : (@List.{0} (@Nat)) := (let _v2 : (@List.{0} (@Nat)) := (let _v2 : (@List.{0} (@Nat)) := (let _v2 : (@List.{0}
  (@Nat)) := (let _v2 : (@List.{0} (@Nat)) := (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3327 : Nat) (@instOfNatNat
  (3327 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (361 : Nat) (@instOfNatNat (361 : Nat))) (@List.cons.{0}
  (@Nat) (@OfNat.ofNat.{0} (@Nat) (3333 : Nat) (@instOfNatNat (3333 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0}
  (@Nat) (367 : Nat) (@instOfNatNat (367 : Nat))) _v1))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3306 : Nat) (@instOfNatNat (3306 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3309 : Nat) (@instOfNatNat (3309 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3321 : Nat) (@instOfNatNat (3321 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3324 : Nat) (@instOfNatNat
  (3324 : Nat))) _v2)))));
(let _v3 : (@List.{0} (@Nat)) := (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3303 : Nat) (@instOfNatNat (3303 :
  Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3306 : Nat) (@instOfNatNat (3306 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3309 : Nat) (@instOfNatNat (3309 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3313 : Nat) (@instOfNatNat (3313 : Nat))) _v2))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3291 : Nat) (@instOfNatNat (3291 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3295 : Nat) (@instOfNatNat (3295 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3288 : Nat) (@instOfNatNat (3288 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3291 : Nat) (@instOfNatNat
  (3291 : Nat))) _v3))))));
(let _v3 : (@List.{0} (@Nat)) := (let _v3 : (@List.{0} (@Nat)) := (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3270
  : Nat) (@instOfNatNat (3270 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3273 : Nat) (@instOfNatNat (3273 :
  Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3285 : Nat) (@instOfNatNat (3285 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3288 : Nat) (@instOfNatNat (3288 : Nat))) _v2))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3267 : Nat) (@instOfNatNat (3267 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3270 : Nat) (@instOfNatNat (3270 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3273 : Nat) (@instOfNatNat (3273 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3277 : Nat) (@instOfNatNat
  (3277 : Nat))) _v3)))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3237 : Nat) (@instOfNatNat (3237 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3249 : Nat) (@instOfNatNat (3249 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3252 : Nat) (@instOfNatNat (3252 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3255 : Nat) (@instOfNatNat
  (3255 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3259 : Nat) (@instOfNatNat (3259 : Nat)))
  (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3252 : Nat) (@instOfNatNat (3252 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3255 : Nat) (@instOfNatNat (3255 : Nat))) _v3)))))))));
(let _v3 : (@List.{0} (@Nat)) := (let _v3 : (@List.{0} (@Nat)) := (let _v3 : (@List.{0} (@Nat)) := (@List.cons.{0}
  (@Nat) (@OfNat.ofNat.{0} (@Nat) (3225 : Nat) (@instOfNatNat (3225 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0}
  (@Nat) (3228 : Nat) (@instOfNatNat (3228 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3628 : Nat)
  (@instOfNatNat (3628 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3234 : Nat) (@instOfNatNat (3234 : Nat)))
  _v2))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3231 : Nat) (@instOfNatNat (3231 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3228 : Nat) (@instOfNatNat (3228 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3221 : Nat) (@instOfNatNat (3221 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3241 : Nat) (@instOfNatNat
  (3241 : Nat))) _v3)))));
(let _v4 : (@List.{0} (@Nat)) := (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3203 : Nat) (@instOfNatNat (3203 :
  Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3215 : Nat) (@instOfNatNat (3215 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3218 : Nat) (@instOfNatNat (3218 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3221 : Nat) (@instOfNatNat (3221 : Nat))) _v3))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3200 : Nat) (@instOfNatNat (3200 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3203 : Nat) (@instOfNatNat (3203 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3205 : Nat) (@instOfNatNat (3205 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3200 : Nat) (@instOfNatNat
  (3200 : Nat))) _v4))))));
(let _v4 : (@List.{0} (@Nat)) := (let _v4 : (@List.{0} (@Nat)) := (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3187
  : Nat) (@instOfNatNat (3187 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3182 : Nat) (@instOfNatNat (3182 :
  Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3185 : Nat) (@instOfNatNat (3185 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3197 : Nat) (@instOfNatNat (3197 : Nat))) _v3))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3167 : Nat) (@instOfNatNat (3167 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3179 : Nat) (@instOfNatNat (3179 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3182 : Nat) (@instOfNatNat (3182 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3185 : Nat) (@instOfNatNat
  (3185 : Nat))) _v4)))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3146 : Nat) (@instOfNatNat (3146 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3149 : Nat) (@instOfNatNat (3149 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3161 : Nat) (@instOfNatNat (3161 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3164 : Nat) (@instOfNatNat
  (3164 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3167 : Nat) (@instOfNatNat (3167 : Nat)))
  (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3169 : Nat) (@instOfNatNat (3169 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3164 : Nat) (@instOfNatNat (3164 : Nat))) _v4))))))))));
(let _v3 : (@List.{0} (@Nat)) := (let _v3 : (@List.{0} (@Nat)) := (let _v3 : (@List.{0} (@Nat)) := (let _v3 : (@List.{0}
  (@Nat)) := (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3143 : Nat) (@instOfNatNat (3143 : Nat))) (@List.cons.{0}
  (@Nat) (@OfNat.ofNat.{0} (@Nat) (3146 : Nat) (@instOfNatNat (3146 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0}
  (@Nat) (3149 : Nat) (@instOfNatNat (3149 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3151 : Nat)
  (@instOfNatNat (3151 : Nat))) _v2))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3131 : Nat) (@instOfNatNat (3131 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3125 : Nat) (@instOfNatNat (3125 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3137 : Nat) (@instOfNatNat (3137 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3131 : Nat) (@instOfNatNat
  (3131 : Nat))) _v3)))));
(let _v4 : (@List.{0} (@Nat)) := (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3110 : Nat) (@instOfNatNat (3110 :
  Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3113 : Nat) (@instOfNatNat (3113 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3125 : Nat) (@instOfNatNat (3125 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3128 : Nat) (@instOfNatNat (3128 : Nat))) _v3))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3350 : Nat) (@instOfNatNat (3350 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3113 : Nat) (@instOfNatNat (3113 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3102 : Nat) (@instOfNatNat (3102 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3115 : Nat) (@instOfNatNat
  (3115 : Nat))) _v4))))));
(let _v4 : (@List.{0} (@Nat)) := (let _v4 : (@List.{0} (@Nat)) := (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3084
  : Nat) (@instOfNatNat (3084 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3096 : Nat) (@instOfNatNat (3096 :
  Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3099 : Nat) (@instOfNatNat (3099 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3102 : Nat) (@instOfNatNat (3102 : Nat))) _v3))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (364 : Nat) (@instOfNatNat (364 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3084 : Nat) (@instOfNatNat (3084 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3088 : Nat) (@instOfNatNat (3088 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (364 : Nat) (@instOfNatNat
  (364 : Nat))) _v4)))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3060 : Nat) (@instOfNatNat (3060 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3063 : Nat) (@instOfNatNat (3063 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3066 : Nat) (@instOfNatNat (3066 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (361 : Nat) (@instOfNatNat
  (361 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3072 : Nat) (@instOfNatNat (3072 : Nat))) (@List.cons.{0}
  (@Nat) (@OfNat.ofNat.{0} (@Nat) (367 : Nat) (@instOfNatNat (367 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3069 : Nat) (@instOfNatNat (3069 : Nat))) _v4)))))))));
(let _v4 : (@List.{0} (@Nat)) := (let _v4 : (@List.{0} (@Nat)) := (let _v4 : (@List.{0} (@Nat)) := (@List.cons.{0}
  (@Nat) (@OfNat.ofNat.{0} (@Nat) (3048 : Nat) (@instOfNatNat (3048 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0}
  (@Nat) (3052 : Nat) (@instOfNatNat (3052 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3045 : Nat)
  (@instOfNatNat (3045 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3048 : Nat) (@instOfNatNat (3048 : Nat)))
  _v3))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3027 : Nat) (@instOfNatNat (3027 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3030 : Nat) (@instOfNatNat (3030 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3042 : Nat) (@instOfNatNat (3042 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3045 : Nat) (@instOfNatNat
  (3045 : Nat))) _v4)))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3016 : Nat) (@instOfNatNat (3016 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3009 : Nat) (@instOfNatNat (3009 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (3012 : Nat) (@instOfNatNat (3012 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3024 : Nat) (@instOfNatNat
  (3024 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3027 : Nat) (@instOfNatNat (3027 : Nat)))
  (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3030 : Nat) (@instOfNatNat (3030 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3034 : Nat) (@instOfNatNat (3034 : Nat))) _v4))))))));
(let _v5 : (@List.{0} (@Nat)) := (let _v5 : (@List.{0} (@Nat)) := (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (2994
  : Nat) (@instOfNatNat (2994 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3006 : Nat) (@instOfNatNat (3006 :
  Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (3009 : Nat) (@instOfNatNat (3009 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3012 : Nat) (@instOfNatNat (3012 : Nat))) _v4))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (364 : Nat) (@instOfNatNat (364 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (2991 : Nat) (@instOfNatNat (2991 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (2998 : Nat) (@instOfNatNat (2998 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (2991 : Nat) (@instOfNatNat
  (2991 : Nat))) _v5)))));
(@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (2972 : Nat) (@instOfNatNat (2972 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (2975 : Nat) (@instOfNatNat (2975 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat)
  (2978 : Nat) (@instOfNatNat (2978 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (2979 : Nat) (@instOfNatNat
  (2979 : Nat))) (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (2982 : Nat) (@instOfNatNat (2982 : Nat)))
  (@List.cons.{0} (@Nat) (@OfNat.ofNat.{0} (@Nat) (2978 : Nat) (@instOfNatNat (2978 : Nat))) (@List.cons.{0} (@Nat)
  (@OfNat.ofNat.{0} (@Nat) (3430 : Nat) (@instOfNatNat (3430 : Nat))) _v5)))))))))))))) := by
  exact @CappedWeight.check_instructions_equation
