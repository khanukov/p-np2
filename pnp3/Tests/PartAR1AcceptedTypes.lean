import Tests.PartAR1LiteralPilot

set_option autoImplicit false

-- Independent literal expected type: AcceptedBody.AcceptedOrbit.
noncomputable def PartACanonical.Types.p0001 :
(∀ (_v0 : (@Nat)),
(Sort 0)) := by
  exact @AcceptedBody.AcceptedOrbit

-- Independent literal expected type: AcceptedBody.Parsed.
noncomputable def PartACanonical.Types.p0002 :
(∀ (_v0 : (@Nat)),
(Sort (0 + 1))) := by
  exact @AcceptedBody.Parsed

-- Independent literal expected type: AcceptedBody.clock_bound.
noncomputable def PartACanonical.Types.p0003 :
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
  (@Body.iterClock (@List.replicate.{0} (@Bool) _v1 (@Bool.false)) _v2)) (@AcceptedBody.deadline _v0))))))))) := by
  exact @AcceptedBody.clock_bound

-- Independent literal expected type: AcceptedBody.concat_eq_append.
noncomputable def PartACanonical.Types.p0004 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ (_v2 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v0)),
(∀ (_v3 : (@Pnp3.Complexity.Uniform.V1.Bitstring _v1)),
(@Eq.{(0 + 1)} (@Pnp4.Frontier.ContractExpansion.PrefixBitVec (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) _v0 _v1)) (@Pnp4.Frontier.ContractExpansion.PartAEndpoint.concatV1ToPrefixBitVec _v0 _v1 _v2 _v3)
  (@Fin.append.{(0 + 1)} _v0 _v1 (@Bool) _v2 _v3)))))) := by
  exact @AcceptedBody.concat_eq_append

-- Independent literal expected type: AcceptedBody.deadline.
noncomputable def PartACanonical.Types.p0005 :
(∀ (_v0 : (@Nat)),
(@Nat)) := by
  exact @AcceptedBody.deadline

-- Independent literal expected type: AcceptedBody.exact.
noncomputable def PartACanonical.Types.p0006 :
(∀ (_v0 : (@Nat)),
(@AcceptedBody.AcceptedOrbit _v0)) := by
  exact @AcceptedBody.exact

-- Independent literal expected type: AcceptedBody.strict_capacity.
noncomputable def PartACanonical.Types.p0007 :
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
(@LT.lt.{0} (@Nat) (@instLTNat) _v3 (@Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.capacity _v0 _v1 _v2)))))))))) := by
  exact @AcceptedBody.strict_capacity

-- Independent literal expected type: AcceptedBody.table_support.
noncomputable def PartACanonical.Types.p0008 :
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v6))) _v3))) _v1))))))) := by
  exact @AcceptedBody.table_support

-- Independent literal expected type: Body.Edge.
noncomputable def PartACanonical.Types.p0077 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Body.Node)),
(∀ (_v2 : (@Body.Node)),
(Sort 0)))) := by
  exact @Body.Edge

-- Independent literal expected type: Body.Edge.after.
noncomputable def PartACanonical.Types.p0078 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Body.Node)},
(∀ {_v2 : (@Body.Node)},
(∀ (_v3 : (@Body.Edge _v0 _v1 _v2)),
(@LE.le.{0} (@Nat) (@instLENat) (@Body.Node.head _v2) _v0))))) := by
  exact @Body.Edge.after

-- Independent literal expected type: Body.Edge.before.
noncomputable def PartACanonical.Types.p0079 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Body.Node)},
(∀ {_v2 : (@Body.Node)},
(∀ (_v3 : (@Body.Edge _v0 _v1 _v2)),
(@LE.le.{0} (@Nat) (@instLENat) (@Body.Node.head _v1) _v0))))) := by
  exact @Body.Edge.before

-- Independent literal expected type: Body.Edge.casesOn.
noncomputable def PartACanonical.Types.p0080.{u} :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Body.Node)},
(∀ {_v2 : (@Body.Node)},
(∀ {_v3 : (∀ (_v3 : (@Body.Edge _v0 _v1 _v2)),
(Sort u))},
(∀ (_v4 : (@Body.Edge _v0 _v1 _v2)),
(∀ (_v5 : (∀ (_v5 : (@LE.le.{0} (@Nat) (@instLENat) (@Body.Node.head _v1) _v0)),
(∀ (_v6 : (@LE.le.{0} (@Nat) (@instLENat) (@Body.Node.head _v2) _v0)),
(∀ (_v7 : (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.machine))) (@Prod.fst.{0, 0}
  (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.machine))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Body.machine) (@Body.Node.state _v1)
  (@Body.Node.tape _v1 (@Body.Node.head _v1)))) (@Body.Node.state _v2))),
(∀ (_v8 : (@Eq.{(0 + 1)} (@Nat) (@Body.dest (@Body.Node.head _v1) (@Prod.snd.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move) (@Prod.snd.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Body.machine))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Body.machine) (@Body.Node.state _v1) (@Body.Node.tape _v1 (@Body.Node.head
  _v1)))))) (@Body.Node.head _v2))),
(∀ (_v9 : (@Eq.{(0 + 1)} (∀ (_v9 : (@Nat)),
(@Option.{0} (@Bool))) (@Body.Node.tape _v2) (@Body.put (@Body.Node.tape _v1) (@Body.Node.head _v1) (@Prod.fst.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Prod.snd.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.machine))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Body.machine) (@Body.Node.state _v1)
  (@Body.Node.tape _v1 (@Body.Node.head _v1)))))))),
(@_v3 (@Body.Edge.mk _v0 _v1 _v2 _v5 _v6 _v7 _v8 _v9)))))))),
(@_v3 _v4))))))) := by
  exact @Body.Edge.casesOn.{u}

-- Independent literal expected type: Body.Edge.mk.
noncomputable def PartACanonical.Types.p0081 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Body.Node)},
(∀ {_v2 : (@Body.Node)},
(∀ (_v3 : (@LE.le.{0} (@Nat) (@instLENat) (@Body.Node.head _v1) _v0)),
(∀ (_v4 : (@LE.le.{0} (@Nat) (@instLENat) (@Body.Node.head _v2) _v0)),
(∀ (_v5 : (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.machine))) (@Prod.fst.{0, 0}
  (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.machine))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Body.machine) (@Body.Node.state _v1)
  (@Body.Node.tape _v1 (@Body.Node.head _v1)))) (@Body.Node.state _v2))),
(∀ (_v6 : (@Eq.{(0 + 1)} (@Nat) (@Body.dest (@Body.Node.head _v1) (@Prod.snd.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move) (@Prod.snd.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Body.machine))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Body.machine) (@Body.Node.state _v1) (@Body.Node.tape _v1 (@Body.Node.head
  _v1)))))) (@Body.Node.head _v2))),
(∀ (_v7 : (@Eq.{(0 + 1)} (∀ (_v7 : (@Nat)),
(@Option.{0} (@Bool))) (@Body.Node.tape _v2) (@Body.put (@Body.Node.tape _v1) (@Body.Node.head _v1) (@Prod.fst.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Prod.snd.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.machine))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Body.machine) (@Body.Node.state _v1)
  (@Body.Node.tape _v1 (@Body.Node.head _v1)))))))),
(@Body.Edge _v0 _v1 _v2))))))))) := by
  exact @Body.Edge.mk

-- Independent literal expected type: Body.Edge.move.
noncomputable def PartACanonical.Types.p0082 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Body.Node)},
(∀ {_v2 : (@Body.Node)},
(∀ (_v3 : (@Body.Edge _v0 _v1 _v2)),
(@Eq.{(0 + 1)} (@Nat) (@Body.dest (@Body.Node.head _v1) (@Prod.snd.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move) (@Prod.snd.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Body.machine))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Body.machine) (@Body.Node.state _v1) (@Body.Node.tape _v1 (@Body.Node.head
  _v1)))))) (@Body.Node.head _v2)))))) := by
  exact @Body.Edge.move

-- Independent literal expected type: Body.Edge.noConfusion.
noncomputable def PartACanonical.Types.p0083.{u} :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Body.Node)},
(∀ {_v2 : (@Body.Node)},
(∀ {_v3 : (Sort u)},
(∀ {_v4 : (@Body.Edge _v0 _v1 _v2)},
(∀ {_v5 : (@Body.Edge _v0 _v1 _v2)},
(∀ (_v6 : (@Eq.{0} (@Body.Edge _v0 _v1 _v2) _v4 _v5)),
(@Body.Edge.noConfusionType.{u} _v0 _v1 _v2 _v3 _v4 _v5)))))))) := by
  exact @Body.Edge.noConfusion.{u}

-- Independent literal expected type: Body.Edge.noConfusionType.
noncomputable def PartACanonical.Types.p0084.{u} :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Body.Node)},
(∀ {_v2 : (@Body.Node)},
(∀ (_v3 : (Sort u)),
(∀ (_v4 : (@Body.Edge _v0 _v1 _v2)),
(∀ (_v5 : (@Body.Edge _v0 _v1 _v2)),
(Sort u))))))) := by
  exact @Body.Edge.noConfusionType.{u}

-- Independent literal expected type: Body.Edge.noConfusionType.withCtor.
noncomputable def PartACanonical.Types.p0085.{u} :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Body.Node)),
(∀ (_v2 : (@Body.Node)),
(∀ (_v3 : (Sort (u + 1))),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Body.Edge.noConfusionType.withCtorType.{u} _v0 _v1 _v2 _v3 _v4)),
(∀ (_v6 : _v3),
(∀ (_v7 : (@Body.Edge _v0 _v1 _v2)),
_v3)))))))) := by
  exact @Body.Edge.noConfusionType.withCtor.{u}

-- Independent literal expected type: Body.Edge.noConfusionType.withCtorType.
noncomputable def PartACanonical.Types.p0086.{u} :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Body.Node)),
(∀ (_v2 : (@Body.Node)),
(∀ (_v3 : (Sort (u + 1))),
(∀ (_v4 : (@Nat)),
(Sort (u + 1))))))) := by
  exact @Body.Edge.noConfusionType.withCtorType.{u}

-- Independent literal expected type: Body.Edge.rec.
noncomputable def PartACanonical.Types.p0087.{u} :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Body.Node)},
(∀ {_v2 : (@Body.Node)},
(∀ {_v3 : (∀ (_v3 : (@Body.Edge _v0 _v1 _v2)),
(Sort u))},
(∀ (_v4 : (∀ (_v4 : (@LE.le.{0} (@Nat) (@instLENat) (@Body.Node.head _v1) _v0)),
(∀ (_v5 : (@LE.le.{0} (@Nat) (@instLENat) (@Body.Node.head _v2) _v0)),
(∀ (_v6 : (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.machine))) (@Prod.fst.{0, 0}
  (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.machine))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Body.machine) (@Body.Node.state _v1)
  (@Body.Node.tape _v1 (@Body.Node.head _v1)))) (@Body.Node.state _v2))),
(∀ (_v7 : (@Eq.{(0 + 1)} (@Nat) (@Body.dest (@Body.Node.head _v1) (@Prod.snd.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move) (@Prod.snd.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Body.machine))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Body.machine) (@Body.Node.state _v1) (@Body.Node.tape _v1 (@Body.Node.head
  _v1)))))) (@Body.Node.head _v2))),
(∀ (_v8 : (@Eq.{(0 + 1)} (∀ (_v8 : (@Nat)),
(@Option.{0} (@Bool))) (@Body.Node.tape _v2) (@Body.put (@Body.Node.tape _v1) (@Body.Node.head _v1) (@Prod.fst.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Prod.snd.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.machine))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Body.machine) (@Body.Node.state _v1)
  (@Body.Node.tape _v1 (@Body.Node.head _v1)))))))),
(@_v3 (@Body.Edge.mk _v0 _v1 _v2 _v4 _v5 _v6 _v7 _v8)))))))),
(∀ (_v5 : (@Body.Edge _v0 _v1 _v2)),
(@_v3 _v5))))))) := by
  exact @Body.Edge.rec.{u}

-- Independent literal expected type: Body.Edge.recOn.
noncomputable def PartACanonical.Types.p0088.{u} :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Body.Node)},
(∀ {_v2 : (@Body.Node)},
(∀ {_v3 : (∀ (_v3 : (@Body.Edge _v0 _v1 _v2)),
(Sort u))},
(∀ (_v4 : (@Body.Edge _v0 _v1 _v2)),
(∀ (_v5 : (∀ (_v5 : (@LE.le.{0} (@Nat) (@instLENat) (@Body.Node.head _v1) _v0)),
(∀ (_v6 : (@LE.le.{0} (@Nat) (@instLENat) (@Body.Node.head _v2) _v0)),
(∀ (_v7 : (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.machine))) (@Prod.fst.{0, 0}
  (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.machine))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Body.machine) (@Body.Node.state _v1)
  (@Body.Node.tape _v1 (@Body.Node.head _v1)))) (@Body.Node.state _v2))),
(∀ (_v8 : (@Eq.{(0 + 1)} (@Nat) (@Body.dest (@Body.Node.head _v1) (@Prod.snd.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move) (@Prod.snd.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@Body.machine))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Body.machine) (@Body.Node.state _v1) (@Body.Node.tape _v1 (@Body.Node.head
  _v1)))))) (@Body.Node.head _v2))),
(∀ (_v9 : (@Eq.{(0 + 1)} (∀ (_v9 : (@Nat)),
(@Option.{0} (@Bool))) (@Body.Node.tape _v2) (@Body.put (@Body.Node.tape _v1) (@Body.Node.head _v1) (@Prod.fst.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Prod.snd.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.machine))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Body.machine) (@Body.Node.state _v1)
  (@Body.Node.tape _v1 (@Body.Node.head _v1)))))))),
(@_v3 (@Body.Edge.mk _v0 _v1 _v2 _v5 _v6 _v7 _v8 _v9)))))))),
(@_v3 _v4))))))) := by
  exact @Body.Edge.recOn.{u}

-- Independent literal expected type: Body.Edge.row.
noncomputable def PartACanonical.Types.p0089 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Body.Node)},
(∀ {_v2 : (@Body.Node)},
(∀ (_v3 : (@Body.Edge _v0 _v1 _v2)),
(@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.machine))) (@Prod.fst.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.machine))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Body.machine) (@Body.Node.state _v1)
  (@Body.Node.tape _v1 (@Body.Node.head _v1)))) (@Body.Node.state _v2)))))) := by
  exact @Body.Edge.row

-- Independent literal expected type: Body.Edge.tape.
noncomputable def PartACanonical.Types.p0090 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Body.Node)},
(∀ {_v2 : (@Body.Node)},
(∀ (_v3 : (@Body.Edge _v0 _v1 _v2)),
(@Eq.{(0 + 1)} (∀ (_v4 : (@Nat)),
(@Option.{0} (@Bool))) (@Body.Node.tape _v2) (@Body.put (@Body.Node.tape _v1) (@Body.Node.head _v1) (@Prod.fst.{0, 0}
  (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Prod.snd.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@Body.machine))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@Body.machine) (@Body.Node.state _v1)
  (@Body.Node.tape _v1 (@Body.Node.head _v1))))))))))) := by
  exact @Body.Edge.tape

-- Independent literal expected type: Body.Good.
noncomputable def PartACanonical.Types.p0091 :
(∀ (_v0 : (@List.{0} (@Bool))),
(∀ (_v1 : (@Nat)),
(Sort 0))) := by
  exact @Body.Good

-- Independent literal expected type: Body.Node.
noncomputable def PartACanonical.Types.p0092 :
(Sort (0 + 1)) := by
  exact @Body.Node

-- Independent literal expected type: Body.Node.casesOn.
noncomputable def PartACanonical.Types.p0093.{u} :
(∀ {_v0 : (∀ (_v0 : (@Body.Node)),
(Sort u))},
(∀ (_v1 : (@Body.Node)),
(∀ (_v2 : (∀ (_v2 : (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))))),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (∀ (_v4 : (@Nat)),
(@Option.{0} (@Bool)))),
(@_v0 (@Body.Node.mk _v2 _v3 _v4)))))),
(@_v0 _v1)))) := by
  exact @Body.Node.casesOn.{u}

-- Independent literal expected type: Body.Node.head.
noncomputable def PartACanonical.Types.p0094 :
(∀ (_v0 : (@Body.Node)),
(@Nat)) := by
  exact @Body.Node.head

-- Independent literal expected type: Body.Node.mk.
noncomputable def PartACanonical.Types.p0095 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (∀ (_v2 : (@Nat)),
(@Option.{0} (@Bool)))),
(@Body.Node)))) := by
  exact @Body.Node.mk

-- Independent literal expected type: Body.Node.mk.inj.
noncomputable def PartACanonical.Types.p0096 :
(∀ {_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))))},
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (∀ (_v2 : (@Nat)),
(@Option.{0} (@Bool)))},
(∀ {_v3 : (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))))},
(∀ {_v4 : (@Nat)},
(∀ {_v5 : (∀ (_v5 : (@Nat)),
(@Option.{0} (@Bool)))},
(∀ (_v6 : (@Eq.{(0 + 1)} (@Body.Node) (@Body.Node.mk _v0 _v1 _v2) (@Body.Node.mk _v3 _v4 _v5))),
(@And (@Eq.{(0 + 1)} (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))) _v0 _v3) (@And (@Eq.{(0 + 1)}
  (@Nat) _v1 _v4) (@Eq.{(0 + 1)} (∀ (_v7 : (@Nat)),
(@Option.{0} (@Bool))) _v2 _v5)))))))))) := by
  exact @Body.Node.mk.inj

-- Independent literal complete proposition: Body.Node.mk.inj.
theorem PartACanonical.Surface.m0060 :
(∀ {_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))))},
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (∀ (_v2 : (@Nat)),
(@Option.{0} (@Bool)))},
(∀ {_v3 : (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))))},
(∀ {_v4 : (@Nat)},
(∀ {_v5 : (∀ (_v5 : (@Nat)),
(@Option.{0} (@Bool)))},
(∀ (_v6 : (@Eq.{(0 + 1)} (@Body.Node) (@Body.Node.mk _v0 _v1 _v2) (@Body.Node.mk _v3 _v4 _v5))),
(@And (@Eq.{(0 + 1)} (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))) _v0 _v3) (@And (@Eq.{(0 + 1)}
  (@Nat) _v1 _v4) (@Eq.{(0 + 1)} (∀ (_v7 : (@Nat)),
(@Option.{0} (@Bool))) _v2 _v5)))))))))) := by
  exact @Body.Node.mk.inj

-- Independent literal expected type: Body.Node.mk.injEq.
noncomputable def PartACanonical.Types.p0097 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (∀ (_v2 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v3 : (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))))),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (∀ (_v5 : (@Nat)),
(@Option.{0} (@Bool)))),
(@Eq.{(0 + 1)} (Sort 0) (@Eq.{(0 + 1)} (@Body.Node) (@Body.Node.mk _v0 _v1 _v2) (@Body.Node.mk _v3 _v4 _v5)) (@And
  (@Eq.{(0 + 1)} (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))) _v0 _v3) (@And (@Eq.{(0 + 1)} (@Nat)
  _v1 _v4) (@Eq.{(0 + 1)} (∀ (_v6 : (@Nat)),
(@Option.{0} (@Bool))) _v2 _v5)))))))))) := by
  exact @Body.Node.mk.injEq

-- Independent literal complete proposition: Body.Node.mk.injEq.
theorem PartACanonical.Surface.m0061 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (∀ (_v2 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v3 : (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))))),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (∀ (_v5 : (@Nat)),
(@Option.{0} (@Bool)))),
(@Eq.{(0 + 1)} (Sort 0) (@Eq.{(0 + 1)} (@Body.Node) (@Body.Node.mk _v0 _v1 _v2) (@Body.Node.mk _v3 _v4 _v5)) (@And
  (@Eq.{(0 + 1)} (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))) _v0 _v3) (@And (@Eq.{(0 + 1)} (@Nat)
  _v1 _v4) (@Eq.{(0 + 1)} (∀ (_v6 : (@Nat)),
(@Option.{0} (@Bool))) _v2 _v5)))))))))) := by
  exact @Body.Node.mk.injEq

-- Independent literal expected type: Body.Node.mk.sizeOf_spec.
noncomputable def PartACanonical.Types.p0098 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (∀ (_v2 : (@Nat)),
(@Option.{0} (@Bool)))),
(@Eq.{(0 + 1)} (@Nat) (@SizeOf.sizeOf.{(0 + 1)} (@Body.Node) (@Body.Node._sizeOf_inst) (@Body.Node.mk _v0 _v1 _v2))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))
  (@SizeOf.sizeOf.{(0 + 1)} (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))) (@Fin._sizeOf_inst
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))) _v0)) (@SizeOf.sizeOf.{(0 + 1)} (@Nat) (@instSizeOfNat)
  _v1)))))) := by
  exact @Body.Node.mk.sizeOf_spec

-- Independent literal complete proposition: Body.Node.mk.sizeOf_spec.
theorem PartACanonical.Surface.m0062 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (∀ (_v2 : (@Nat)),
(@Option.{0} (@Bool)))),
(@Eq.{(0 + 1)} (@Nat) (@SizeOf.sizeOf.{(0 + 1)} (@Body.Node) (@Body.Node._sizeOf_inst) (@Body.Node.mk _v0 _v1 _v2))
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))
  (@SizeOf.sizeOf.{(0 + 1)} (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))) (@Fin._sizeOf_inst
  (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))) _v0)) (@SizeOf.sizeOf.{(0 + 1)} (@Nat) (@instSizeOfNat)
  _v1)))))) := by
  exact @Body.Node.mk.sizeOf_spec

-- Independent literal expected type: Body.Node.noConfusion.
noncomputable def PartACanonical.Types.p0099.{u} :
(∀ {_v0 : (Sort u)},
(∀ {_v1 : (@Body.Node)},
(∀ {_v2 : (@Body.Node)},
(∀ (_v3 : (@Eq.{(0 + 1)} (@Body.Node) _v1 _v2)),
(@Body.Node.noConfusionType.{u} _v0 _v1 _v2))))) := by
  exact @Body.Node.noConfusion.{u}

-- Independent literal expected type: Body.Node.noConfusionType.
noncomputable def PartACanonical.Types.p0100.{u} :
(∀ (_v0 : (Sort u)),
(∀ (_v1 : (@Body.Node)),
(∀ (_v2 : (@Body.Node)),
(Sort u)))) := by
  exact @Body.Node.noConfusionType.{u}

-- Independent literal expected type: Body.Node.noConfusionType.withCtor.
noncomputable def PartACanonical.Types.p0101.{u} :
(∀ (_v0 : (Sort (u + 1))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Body.Node.noConfusionType.withCtorType.{u} _v0 _v1)),
(∀ (_v3 : _v0),
(∀ (_v4 : (@Body.Node)),
_v0))))) := by
  exact @Body.Node.noConfusionType.withCtor.{u}

-- Independent literal expected type: Body.Node.noConfusionType.withCtorType.
noncomputable def PartACanonical.Types.p0102.{u} :
(∀ (_v0 : (Sort (u + 1))),
(∀ (_v1 : (@Nat)),
(Sort (max ((0 + 1) + 1) (u + 1))))) := by
  exact @Body.Node.noConfusionType.withCtorType.{u}

-- Independent literal expected type: Body.Node.recOn.
noncomputable def PartACanonical.Types.p0104.{u} :
(∀ {_v0 : (∀ (_v0 : (@Body.Node)),
(Sort u))},
(∀ (_v1 : (@Body.Node)),
(∀ (_v2 : (∀ (_v2 : (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))))),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (∀ (_v4 : (@Nat)),
(@Option.{0} (@Bool)))),
(@_v0 (@Body.Node.mk _v2 _v3 _v4)))))),
(@_v0 _v1)))) := by
  exact @Body.Node.recOn.{u}

-- Independent literal expected type: Body.Node.state.
noncomputable def PartACanonical.Types.p0105 :
(∀ (_v0 : (@Body.Node)),
(@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))))) := by
  exact @Body.Node.state

-- Independent literal expected type: Body.Node.tape.
noncomputable def PartACanonical.Types.p0106 :
(∀ (_v0 : (@Body.Node)),
(∀ (_v1 : (@Nat)),
(@Option.{0} (@Bool)))) := by
  exact @Body.Node.tape

-- Independent literal expected type: Body.Path.
noncomputable def PartACanonical.Types.p0107 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Body.Node)),
(∀ (_v3 : (@Body.Node)),
(Sort 0))))) := by
  exact @Body.Path

-- Independent literal expected type: Body.Path.append.
noncomputable def PartACanonical.Types.p0108 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ {_v3 : (@Body.Node)},
(∀ {_v4 : (@Body.Node)},
(∀ {_v5 : (@Body.Node)},
(∀ (_v6 : (@Body.Path _v0 _v1 _v3 _v4)),
(∀ (_v7 : (@Body.Path _v0 _v2 _v4 _v5)),
(@Body.Path _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v3
  _v5))))))))) := by
  exact @Body.Path.append

-- Independent literal expected type: Body.Path.below.
noncomputable def PartACanonical.Types.p0109 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Body.Node)),
(∀ (_v3 : (@Body.Node)),
(∀ (_v4 : (@Body.Path _v0 _v1 _v2 _v3)),
(Sort 0)))))},
(∀ {_v2 : (@Nat)},
(∀ {_v3 : (@Body.Node)},
(∀ {_v4 : (@Body.Node)},
(∀ (_v5 : (@Body.Path _v0 _v2 _v3 _v4)),
(Sort 0))))))) := by
  exact @Body.Path.below

-- Independent literal expected type: Body.Path.below.casesOn.
noncomputable def PartACanonical.Types.p0110 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Body.Node)),
(∀ (_v3 : (@Body.Node)),
(∀ (_v4 : (@Body.Path _v0 _v1 _v2 _v3)),
(Sort 0)))))},
(∀ {_v2 : (∀ {_v2 : (@Nat)},
(∀ {_v3 : (@Body.Node)},
(∀ {_v4 : (@Body.Node)},
(∀ (_v5 : (@Body.Path _v0 _v2 _v3 _v4)),
(∀ (_v6 : (@Body.Path.below _v0 _v1 _v2 _v3 _v4 _v5)),
(Sort 0))))))},
(∀ {_v3 : (@Nat)},
(∀ {_v4 : (@Body.Node)},
(∀ {_v5 : (@Body.Node)},
(∀ {_v6 : (@Body.Path _v0 _v3 _v4 _v5)},
(∀ (_v7 : (@Body.Path.below _v0 _v1 _v3 _v4 _v5 _v6)),
(∀ (_v8 : (∀ (_v8 : (@Body.Node)),
(∀ (_v9 : (@LE.le.{0} (@Nat) (@instLENat) (@Body.Node.head _v8) _v0)),
(@_v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v8 _v8 (@Body.Path.nil _v0 _v8 _v9)
  (@Body.Path.below.nil _v0 _v1 _v8 _v9))))),
(∀ (_v9 : (∀ {_v9 : (@Nat)},
(∀ {_v10 : (@Body.Node)},
(∀ {_v11 : (@Body.Node)},
(∀ {_v12 : (@Body.Node)},
(∀ (_v13 : (@Body.Edge _v0 _v10 _v11)),
(∀ {_v14 : (@Body.Path _v0 _v9 _v11 _v12)},
(∀ (_v15 : (@Body.Path.below _v0 _v1 _v9 _v11 _v12 _v14)),
(∀ (_v16 : (@_v1 _v9 _v11 _v12 _v14)),
(@_v2 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v9 (@OfNat.ofNat.{0} (@Nat) (1 :
  Nat) (@instOfNatNat (1 : Nat)))) _v10 _v12 (@Body.Path.cons _v0 _v9 _v10 _v11 _v12 _v13 _v14) (@Body.Path.below.cons _v0
  _v1 _v9 _v10 _v11 _v12 _v13 _v14 _v15 _v16))))))))))),
(@_v2 _v3 _v4 _v5 _v6 _v7))))))))))) := by
  exact @Body.Path.below.casesOn

-- Independent literal expected type: Body.Path.below.cons.
noncomputable def PartACanonical.Types.p0111 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Body.Node)),
(∀ (_v3 : (@Body.Node)),
(∀ (_v4 : (@Body.Path _v0 _v1 _v2 _v3)),
(Sort 0)))))},
(∀ {_v2 : (@Nat)},
(∀ {_v3 : (@Body.Node)},
(∀ {_v4 : (@Body.Node)},
(∀ {_v5 : (@Body.Node)},
(∀ (_v6 : (@Body.Edge _v0 _v3 _v4)),
(∀ {_v7 : (@Body.Path _v0 _v2 _v4 _v5)},
(∀ (_v8 : (@Body.Path.below _v0 _v1 _v2 _v4 _v5 _v7)),
(∀ (_v9 : (@_v1 _v2 _v4 _v5 _v7)),
(@Body.Path.below _v0 _v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v3 _v5 (@Body.Path.cons _v0 _v2 _v3 _v4 _v5 _v6
  _v7)))))))))))) := by
  exact @Body.Path.below.cons

-- Independent literal expected type: Body.Path.below.nil.
noncomputable def PartACanonical.Types.p0112 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Body.Node)),
(∀ (_v3 : (@Body.Node)),
(∀ (_v4 : (@Body.Path _v0 _v1 _v2 _v3)),
(Sort 0)))))},
(∀ (_v2 : (@Body.Node)),
(∀ (_v3 : (@LE.le.{0} (@Nat) (@instLENat) (@Body.Node.head _v2) _v0)),
(@Body.Path.below _v0 _v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v2 _v2 (@Body.Path.nil _v0 _v2
  _v3)))))) := by
  exact @Body.Path.below.nil

-- Independent literal expected type: Body.Path.below.rec.
noncomputable def PartACanonical.Types.p0113 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Body.Node)),
(∀ (_v3 : (@Body.Node)),
(∀ (_v4 : (@Body.Path _v0 _v1 _v2 _v3)),
(Sort 0)))))},
(∀ {_v2 : (∀ {_v2 : (@Nat)},
(∀ {_v3 : (@Body.Node)},
(∀ {_v4 : (@Body.Node)},
(∀ (_v5 : (@Body.Path _v0 _v2 _v3 _v4)),
(∀ (_v6 : (@Body.Path.below _v0 _v1 _v2 _v3 _v4 _v5)),
(Sort 0))))))},
(∀ (_v3 : (∀ (_v3 : (@Body.Node)),
(∀ (_v4 : (@LE.le.{0} (@Nat) (@instLENat) (@Body.Node.head _v3) _v0)),
(@_v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v3 _v3 (@Body.Path.nil _v0 _v3 _v4)
  (@Body.Path.below.nil _v0 _v1 _v3 _v4))))),
(∀ (_v4 : (∀ {_v4 : (@Nat)},
(∀ {_v5 : (@Body.Node)},
(∀ {_v6 : (@Body.Node)},
(∀ {_v7 : (@Body.Node)},
(∀ (_v8 : (@Body.Edge _v0 _v5 _v6)),
(∀ {_v9 : (@Body.Path _v0 _v4 _v6 _v7)},
(∀ (_v10 : (@Body.Path.below _v0 _v1 _v4 _v6 _v7 _v9)),
(∀ (_v11 : (@_v1 _v4 _v6 _v7 _v9)),
(∀ (_v12 : (@_v2 _v4 _v6 _v7 _v9 _v10)),
(@_v2 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 (@OfNat.ofNat.{0} (@Nat) (1 :
  Nat) (@instOfNatNat (1 : Nat)))) _v5 _v7 (@Body.Path.cons _v0 _v4 _v5 _v6 _v7 _v8 _v9) (@Body.Path.below.cons _v0 _v1
  _v4 _v5 _v6 _v7 _v8 _v9 _v10 _v11)))))))))))),
(∀ {_v5 : (@Nat)},
(∀ {_v6 : (@Body.Node)},
(∀ {_v7 : (@Body.Node)},
(∀ {_v8 : (@Body.Path _v0 _v5 _v6 _v7)},
(∀ (_v9 : (@Body.Path.below _v0 _v1 _v5 _v6 _v7 _v8)),
(@_v2 _v5 _v6 _v7 _v8 _v9))))))))))) := by
  exact @Body.Path.below.rec

-- Independent literal expected type: Body.Path.bounds.
noncomputable def PartACanonical.Types.p0114 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Body.Node)},
(∀ {_v3 : (@Body.Node)},
(∀ (_v4 : (@Body.Path _v0 _v1 _v2 _v3)),
(@And (@LE.le.{0} (@Nat) (@instLENat) (@Body.Node.head _v2) _v0) (@LE.le.{0} (@Nat) (@instLENat) (@Body.Node.head _v3)
  _v0))))))) := by
  exact @Body.Path.bounds

-- Independent literal expected type: Body.Path.casesOn.
noncomputable def PartACanonical.Types.p0115 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Body.Node)),
(∀ (_v3 : (@Body.Node)),
(∀ (_v4 : (@Body.Path _v0 _v1 _v2 _v3)),
(Sort 0)))))},
(∀ {_v2 : (@Nat)},
(∀ {_v3 : (@Body.Node)},
(∀ {_v4 : (@Body.Node)},
(∀ (_v5 : (@Body.Path _v0 _v2 _v3 _v4)),
(∀ (_v6 : (∀ (_v6 : (@Body.Node)),
(∀ (_v7 : (@LE.le.{0} (@Nat) (@instLENat) (@Body.Node.head _v6) _v0)),
(@_v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v6 _v6 (@Body.Path.nil _v0 _v6 _v7))))),
(∀ (_v7 : (∀ {_v7 : (@Nat)},
(∀ {_v8 : (@Body.Node)},
(∀ {_v9 : (@Body.Node)},
(∀ {_v10 : (@Body.Node)},
(∀ (_v11 : (@Body.Edge _v0 _v8 _v9)),
(∀ (_v12 : (@Body.Path _v0 _v7 _v9 _v10)),
(@_v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v7 (@OfNat.ofNat.{0} (@Nat) (1 :
  Nat) (@instOfNatNat (1 : Nat)))) _v8 _v10 (@Body.Path.cons _v0 _v7 _v8 _v9 _v10 _v11 _v12))))))))),
(@_v1 _v2 _v3 _v4 _v5))))))))) := by
  exact @Body.Path.casesOn

-- Independent literal expected type: Body.Path.cons.
noncomputable def PartACanonical.Types.p0116 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Body.Node)},
(∀ {_v3 : (@Body.Node)},
(∀ {_v4 : (@Body.Node)},
(∀ (_v5 : (@Body.Edge _v0 _v2 _v3)),
(∀ (_v6 : (@Body.Path _v0 _v1 _v3 _v4)),
(@Body.Path _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v2 _v4)))))))) := by
  exact @Body.Path.cons

-- Independent literal expected type: Body.Path.execute.
noncomputable def PartACanonical.Types.p0117 :
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
  (@Body.Path.bounds _v2 _v3 _v4 _v5 _v6)) _v7))))))))))) := by
  exact @Body.Path.execute

-- Independent literal expected type: Body.Path.nil.
noncomputable def PartACanonical.Types.p0118 :
(∀ {_v0 : (@Nat)},
(∀ (_v1 : (@Body.Node)),
(∀ (_v2 : (@LE.le.{0} (@Nat) (@instLENat) (@Body.Node.head _v1) _v0)),
(@Body.Path _v0 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v1 _v1)))) := by
  exact @Body.Path.nil

-- Independent literal expected type: Body.Path.recOn.
noncomputable def PartACanonical.Types.p0120 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Body.Node)),
(∀ (_v3 : (@Body.Node)),
(∀ (_v4 : (@Body.Path _v0 _v1 _v2 _v3)),
(Sort 0)))))},
(∀ {_v2 : (@Nat)},
(∀ {_v3 : (@Body.Node)},
(∀ {_v4 : (@Body.Node)},
(∀ (_v5 : (@Body.Path _v0 _v2 _v3 _v4)),
(∀ (_v6 : (∀ (_v6 : (@Body.Node)),
(∀ (_v7 : (@LE.le.{0} (@Nat) (@instLENat) (@Body.Node.head _v6) _v0)),
(@_v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v6 _v6 (@Body.Path.nil _v0 _v6 _v7))))),
(∀ (_v7 : (∀ {_v7 : (@Nat)},
(∀ {_v8 : (@Body.Node)},
(∀ {_v9 : (@Body.Node)},
(∀ {_v10 : (@Body.Node)},
(∀ (_v11 : (@Body.Edge _v0 _v8 _v9)),
(∀ (_v12 : (@Body.Path _v0 _v7 _v9 _v10)),
(∀ (_v13 : (@_v1 _v7 _v9 _v10 _v12)),
(@_v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v7 (@OfNat.ofNat.{0} (@Nat) (1 :
  Nat) (@instOfNatNat (1 : Nat)))) _v8 _v10 (@Body.Path.cons _v0 _v7 _v8 _v9 _v10 _v11 _v12)))))))))),
(@_v1 _v2 _v3 _v4 _v5))))))))) := by
  exact @Body.Path.recOn

-- Independent literal expected type: Body.Reads.
noncomputable def PartACanonical.Types.p0121 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@List.{0} (@Bool))),
(Sort 0)))) := by
  exact @Body.Reads

-- Independent literal expected type: Body.Reads.eq_1.
noncomputable def PartACanonical.Types.p0122 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@List.{0} (@Bool))),
(@Eq.{(0 + 1)} (Sort 0) (@Body.Reads _v0 _v1 _v2) (∀ (_v3 : (@Nat)),
(∀ (_v4 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 (@List.length.{0} (@Bool) _v2))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v0 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@List.length.{0}
  (@Bool) _v2)) _v3)) (@Option.some.{0} (@Bool) (@GetElem?.getElem!.{0, 0, 0} (@List.{0} (@Bool)) (@Nat) (@Bool) (fun (_v5
  : (@List.{0} (@Bool))) =>
(fun (_v6 : (@Nat)) =>
(@LT.lt.{0} (@Nat) (@instLTNat) _v6 (@List.length.{0} (@Bool) _v5)))) (@List.instGetElem?NatLtLength.{0} (@Bool))
  (@instInhabitedBool) _v2 _v3))))))))) := by
  exact @Body.Reads.eq_1

-- Independent literal complete proposition: Body.Reads.eq_1.
theorem PartACanonical.Surface.m0066 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@List.{0} (@Bool))),
(@Eq.{(0 + 1)} (Sort 0) (@Body.Reads _v0 _v1 _v2) (∀ (_v3 : (@Nat)),
(∀ (_v4 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3 (@List.length.{0} (@Bool) _v2))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v0 (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@List.length.{0}
  (@Bool) _v2)) _v3)) (@Option.some.{0} (@Bool) (@GetElem?.getElem!.{0, 0, 0} (@List.{0} (@Bool)) (@Nat) (@Bool) (fun (_v5
  : (@List.{0} (@Bool))) =>
(fun (_v6 : (@Nat)) =>
(@LT.lt.{0} (@Nat) (@instLTNat) _v6 (@List.length.{0} (@Bool) _v5)))) (@List.instGetElem?NatLtLength.{0} (@Bool))
  (@instInhabitedBool) _v2 _v3))))))))) := by
  exact @Body.Reads.eq_1

-- Independent literal expected type: Body.Target.PartA.
noncomputable def PartACanonical.Types.p0123 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Pnp3.Complexity.Uniform.V1.UniformTM))),
(∀ (_v1 : (∀ (_v1 : (@Nat)),
(@Nat))),
(Sort 0))) := by
  exact @Body.Target.PartA

-- Independent literal expected type: Body.Target.Round.
noncomputable def PartACanonical.Types.p0124 :
(Sort 0) := by
  exact @Body.Target.Round

-- Independent literal expected type: Body.Target.Span.
noncomputable def PartACanonical.Types.p0125 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ (_v2 : (∀ (_v2 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))),
(@Option.{0} (@Bool)))),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@List.{0} (@Bool))),
(Sort 0)))))) := by
  exact @Body.Target.Span

-- Independent literal expected type: Body.carryClock.
noncomputable def PartACanonical.Types.p0126 :
(∀ (_v0 : (@List.{0} (@Bool))),
(∀ (_v1 : (@Nat)),
(@Nat))) := by
  exact @Body.carryClock

-- Independent literal expected type: Body.carryClock.eq_1.
noncomputable def PartACanonical.Types.p0127 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@Body.carryClock (@List.nil.{0} (@Bool)) _v0) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat))))) := by
  exact @Body.carryClock.eq_1

-- Independent literal complete proposition: Body.carryClock.eq_1.
theorem PartACanonical.Surface.m0067 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@Body.carryClock (@List.nil.{0} (@Bool)) _v0) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat
  (1 : Nat))))) := by
  exact @Body.carryClock.eq_1

-- Independent literal expected type: Body.carryClock.eq_2.
noncomputable def PartACanonical.Types.p0128 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@List.{0} (@Bool))),
(@Eq.{(0 + 1)} (@Nat) (@Body.carryClock (@List.cons.{0} (@Bool) (@Bool.false) _v1) _v0) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))))) := by
  exact @Body.carryClock.eq_2

-- Independent literal complete proposition: Body.carryClock.eq_2.
theorem PartACanonical.Surface.m0068 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@List.{0} (@Bool))),
(@Eq.{(0 + 1)} (@Nat) (@Body.carryClock (@List.cons.{0} (@Bool) (@Bool.false) _v1) _v0) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))))))) := by
  exact @Body.carryClock.eq_2

-- Independent literal expected type: Body.carryClock.eq_3.
noncomputable def PartACanonical.Types.p0129 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@List.{0} (@Bool))),
(@Eq.{(0 + 1)} (@Nat) (@Body.carryClock (@List.cons.{0} (@Bool) (@Bool.true) _v1) _v0) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))
  (@Body.carryClock _v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))))) := by
  exact @Body.carryClock.eq_3

-- Independent literal complete proposition: Body.carryClock.eq_3.
theorem PartACanonical.Surface.m0069 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@List.{0} (@Bool))),
(@Eq.{(0 + 1)} (@Nat) (@Body.carryClock (@List.cons.{0} (@Bool) (@Bool.true) _v1) _v0) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))
  (@Body.carryClock _v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))))) := by
  exact @Body.carryClock.eq_3

-- Independent literal expected type: Body.carryTape.
noncomputable def PartACanonical.Types.p0130 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@List.{0} (@Bool))),
(∀ (_v3 : (@Nat)),
(@Option.{0} (@Bool)))))) := by
  exact @Body.carryTape

-- Independent literal expected type: Body.carryTape.eq_1.
noncomputable def PartACanonical.Types.p0131 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(@Eq.{(0 + 1)} (∀ (_v2 : (@Nat)),
(@Option.{0} (@Bool))) (@Body.carryTape _v0 _v1 (@List.nil.{0} (@Bool))) _v0))) := by
  exact @Body.carryTape.eq_1

-- Independent literal complete proposition: Body.carryTape.eq_1.
theorem PartACanonical.Surface.m0070 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(@Eq.{(0 + 1)} (∀ (_v2 : (@Nat)),
(@Option.{0} (@Bool))) (@Body.carryTape _v0 _v1 (@List.nil.{0} (@Bool))) _v0))) := by
  exact @Body.carryTape.eq_1

-- Independent literal expected type: Body.carryTape.eq_2.
noncomputable def PartACanonical.Types.p0132 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@List.{0} (@Bool))),
(@Eq.{(0 + 1)} (∀ (_v3 : (@Nat)),
(@Option.{0} (@Bool))) (@Body.carryTape _v0 _v1 (@List.cons.{0} (@Bool) (@Bool.false) _v2)) (@Body.put _v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@List.length.{0} (@Bool) _v2)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))) (@Option.some.{0} (@Bool) (@Bool.true))))))) := by
  exact @Body.carryTape.eq_2

-- Independent literal complete proposition: Body.carryTape.eq_2.
theorem PartACanonical.Surface.m0071 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@List.{0} (@Bool))),
(@Eq.{(0 + 1)} (∀ (_v3 : (@Nat)),
(@Option.{0} (@Bool))) (@Body.carryTape _v0 _v1 (@List.cons.{0} (@Bool) (@Bool.false) _v2)) (@Body.put _v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@List.length.{0} (@Bool) _v2)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))) (@Option.some.{0} (@Bool) (@Bool.true))))))) := by
  exact @Body.carryTape.eq_2

-- Independent literal expected type: Body.carryTape.eq_3.
noncomputable def PartACanonical.Types.p0133 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@List.{0} (@Bool))),
(@Eq.{(0 + 1)} (∀ (_v3 : (@Nat)),
(@Option.{0} (@Bool))) (@Body.carryTape _v0 _v1 (@List.cons.{0} (@Bool) (@Bool.true) _v2)) (@Body.carryTape (@Body.put
  _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@List.length.{0} (@Bool) _v2)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))) (@Option.some.{0} (@Bool) (@Bool.false))) _v1 _v2))))) := by
  exact @Body.carryTape.eq_3

-- Independent literal complete proposition: Body.carryTape.eq_3.
theorem PartACanonical.Surface.m0072 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@List.{0} (@Bool))),
(@Eq.{(0 + 1)} (∀ (_v3 : (@Nat)),
(@Option.{0} (@Bool))) (@Body.carryTape _v0 _v1 (@List.cons.{0} (@Bool) (@Bool.true) _v2)) (@Body.carryTape (@Body.put
  _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@List.length.{0} (@Bool) _v2)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))) (@Option.some.{0} (@Bool) (@Bool.false))) _v1 _v2))))) := by
  exact @Body.carryTape.eq_3

-- Independent literal expected type: Body.carry_frame.
noncomputable def PartACanonical.Types.p0134 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@List.{0} (@Bool))),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Or (@LE.le.{0} (@Nat) (@instLENat) _v3 _v1) (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@List.length.{0} (@Bool) _v2)) _v3))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Body.carryTape _v0 _v1 _v2 _v3) (@_v0 _v3))))))) := by
  exact @Body.carry_frame

-- Independent literal expected type: Body.carry_path.
noncomputable def PartACanonical.Types.p0135 :
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
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Body.carryTape _v0 _v1 _v3))))))))))) := by
  exact @Body.carry_path

-- Independent literal expected type: Body.carry_reads.
noncomputable def PartACanonical.Types.p0136 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@List.{0} (@Bool))),
(∀ (_v3 : (@Body.Reads _v0 _v1 _v2)),
(@Body.Reads (@Body.carryTape _v0 _v1 _v2) _v1 (@Prod.fst.{0, 0} (@List.{0} (@Bool)) (@Bool) (@Body.inc _v2))))))) := by
  exact @Body.carry_reads

-- Independent literal expected type: Body.clear.
noncomputable def PartACanonical.Types.p0137 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(@Option.{0} (@Bool)))))) := by
  exact @Body.clear

-- Independent literal expected type: Body.clear.eq_1.
noncomputable def PartACanonical.Types.p0138 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Body.clear _v0 _v1 _v2 _v3) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And
  (@LE.le.{0} (@Nat) (@instLENat) _v1 _v3) (@LT.lt.{0} (@Nat) (@instLTNat) _v3 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2))) (@instDecidableAnd (@LE.le.{0} (@Nat) (@instLENat) _v1 _v3) (@LT.lt.{0}
  (@Nat) (@instLTNat) _v3 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2))
  (@Nat.decLe _v1 _v3) (@Nat.decLt _v3 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  _v2))) (@Option.some.{0} (@Bool) (@Bool.false)) (@_v0 _v3))))))) := by
  exact @Body.clear.eq_1

-- Independent literal complete proposition: Body.clear.eq_1.
theorem PartACanonical.Surface.m0076 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (@Nat)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Body.clear _v0 _v1 _v2 _v3) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@And
  (@LE.le.{0} (@Nat) (@instLENat) _v1 _v3) (@LT.lt.{0} (@Nat) (@instLTNat) _v3 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2))) (@instDecidableAnd (@LE.le.{0} (@Nat) (@instLENat) _v1 _v3) (@LT.lt.{0}
  (@Nat) (@instLTNat) _v3 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2))
  (@Nat.decLe _v1 _v3) (@Nat.decLt _v3 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  _v2))) (@Option.some.{0} (@Bool) (@Bool.false)) (@_v0 _v3))))))) := by
  exact @Body.clear.eq_1

-- Independent literal expected type: Body.clear_step.
noncomputable def PartACanonical.Types.p0139 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(@Eq.{(0 + 1)} (∀ (_v3 : (@Nat)),
(@Option.{0} (@Bool))) (@Body.clear (@Body.put _v0 _v1 (@Option.some.{0} (@Bool) (@Bool.false))) (@HAdd.hAdd.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))) _v2) (@Body.clear _v0 _v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))))))) := by
  exact @Body.clear_step

-- Independent literal expected type: Body.dest.
noncomputable def PartACanonical.Types.p0140 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Pnp3.Complexity.Uniform.V1.Move)),
(@Nat))) := by
  exact @Body.dest

-- Independent literal expected type: Body.dest.eq_1.
noncomputable def PartACanonical.Types.p0141 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@Body.dest _v0 (@Pnp3.Complexity.Uniform.V1.Move.left)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) := by
  exact @Body.dest.eq_1

-- Independent literal complete proposition: Body.dest.eq_1.
theorem PartACanonical.Surface.m0078 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@Body.dest _v0 (@Pnp3.Complexity.Uniform.V1.Move.left)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) := by
  exact @Body.dest.eq_1

-- Independent literal expected type: Body.dest.eq_2.
noncomputable def PartACanonical.Types.p0142 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@Body.dest _v0 (@Pnp3.Complexity.Uniform.V1.Move.stay)) _v0)) := by
  exact @Body.dest.eq_2

-- Independent literal complete proposition: Body.dest.eq_2.
theorem PartACanonical.Surface.m0079 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@Body.dest _v0 (@Pnp3.Complexity.Uniform.V1.Move.stay)) _v0)) := by
  exact @Body.dest.eq_2

-- Independent literal expected type: Body.dest.eq_3.
noncomputable def PartACanonical.Types.p0143 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@Body.dest _v0 (@Pnp3.Complexity.Uniform.V1.Move.right)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) := by
  exact @Body.dest.eq_3

-- Independent literal complete proposition: Body.dest.eq_3.
theorem PartACanonical.Surface.m0080 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@Body.dest _v0 (@Pnp3.Complexity.Uniform.V1.Move.right)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) := by
  exact @Body.dest.eq_3

-- Independent literal expected type: Body.embed.
noncomputable def PartACanonical.Types.p0144 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ (_v2 : (@Body.Node)),
(∀ (_v3 : (@LT.lt.{0} (@Nat) (@instLTNat) (@Body.Node.head _v2) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))),
(@Pnp3.Complexity.Uniform.V1.Config (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) _v0 _v1))))) := by
  exact @Body.embed

-- Independent literal expected type: Body.embed.eq_1.
noncomputable def PartACanonical.Types.p0145 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ (_v2 : (@Body.Node)),
(∀ (_v3 : (@LT.lt.{0} (@Nat) (@instLTNat) (@Body.Node.head _v2) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) _v0
  _v1) (@Body.embed _v0 _v1 _v2 _v3) (@Pnp3.Complexity.Uniform.V1.Config.mk (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat))) _v0 _v1 (@Body.Node.state _v2) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)
  (@Body.Node.head _v2) _v3) (fun (_v4 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))) =>
(@Body.Node.tape _v2 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v4))))))))) := by
  exact @Body.embed.eq_1

-- Independent literal complete proposition: Body.embed.eq_1.
theorem PartACanonical.Surface.m0081 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ (_v2 : (@Body.Node)),
(∀ (_v3 : (@LT.lt.{0} (@Nat) (@instLTNat) (@Body.Node.head _v2) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))) _v0
  _v1) (@Body.embed _v0 _v1 _v2 _v3) (@Pnp3.Complexity.Uniform.V1.Config.mk (@OfNat.ofNat.{0} (@Nat) (9 : Nat)
  (@instOfNatNat (9 : Nat))) _v0 _v1 (@Body.Node.state _v2) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)
  (@Body.Node.head _v2) _v3) (fun (_v4 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))) =>
(@Body.Node.tape _v2 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v4))))))))) := by
  exact @Body.embed.eq_1

-- Independent literal expected type: Body.extend.
noncomputable def PartACanonical.Types.p0146 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ (_v2 : (∀ (_v2 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))),
(@Option.{0} (@Bool)))),
(∀ (_v3 : (@Nat)),
(@Option.{0} (@Bool)))))) := by
  exact @Body.extend

-- Independent literal expected type: Body.extend.eq_1.
noncomputable def PartACanonical.Types.p0147 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ (_v2 : (∀ (_v2 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))),
(@Option.{0} (@Bool)))),
(∀ (_v3 : (@Nat)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Body.extend _v0 _v1 _v2 _v3) (@dite.{(0 + 1)} (@Option.{0} (@Bool)) (@LT.lt.{0}
  (@Nat) (@instLTNat) _v3 (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (@Nat.decLt _v3
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (fun (_v4 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))) =>
(@_v2 (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v3 _v4))) (fun (_v4 : (@Not (@LT.lt.{0} (@Nat)
  (@instLTNat) _v3 (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)))) =>
(@Option.none.{0} (@Bool))))))))) := by
  exact @Body.extend.eq_1

-- Independent literal complete proposition: Body.extend.eq_1.
theorem PartACanonical.Surface.m0082 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ (_v2 : (∀ (_v2 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))),
(@Option.{0} (@Bool)))),
(∀ (_v3 : (@Nat)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Body.extend _v0 _v1 _v2 _v3) (@dite.{(0 + 1)} (@Option.{0} (@Bool)) (@LT.lt.{0}
  (@Nat) (@instLTNat) _v3 (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (@Nat.decLt _v3
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)) (fun (_v4 : (@LT.lt.{0} (@Nat) (@instLTNat) _v3
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))) =>
(@_v2 (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v3 _v4))) (fun (_v4 : (@Not (@LT.lt.{0} (@Nat)
  (@instLTNat) _v3 (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1)))) =>
(@Option.none.{0} (@Bool))))))))) := by
  exact @Body.extend.eq_1

-- Independent literal expected type: Body.extend_read.
noncomputable def PartACanonical.Types.p0148 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ (_v2 : (∀ (_v2 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))),
(@Option.{0} (@Bool)))),
(∀ (_v3 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Body.extend _v0 _v1 _v2 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0
  _v1) _v3)) (@_v2 _v3)))))) := by
  exact @Body.extend_read

-- Independent literal expected type: Body.first_accept_whole.
noncomputable def PartACanonical.Types.p0149 :
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
  _v8 _v3) _v5))))))))))))) := by
  exact @Body.first_accept_whole

-- Independent literal expected type: Body.good_of_lt.
noncomputable def PartACanonical.Types.p0150 :
(∀ (_v0 : (@List.{0} (@Bool))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@Body.value _v0) _v1) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat) (@Nat)
  (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  (@List.length.{0} (@Bool) _v0)))),
(@Body.Good _v0 _v1)))) := by
  exact @Body.good_of_lt

-- Independent literal expected type: Body.hop.
noncomputable def PartACanonical.Types.p0151 :
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
  _v2 _v4 (@Body.put _v5 _v3 _v6))))))))))))))) := by
  exact @Body.hop

-- Independent literal expected type: Body.inc.
noncomputable def PartACanonical.Types.p0152 :
(∀ (_v0 : (@List.{0} (@Bool))),
(@Prod.{0, 0} (@List.{0} (@Bool)) (@Bool))) := by
  exact @Body.inc

-- Independent literal expected type: Body.inc.eq_1.
noncomputable def PartACanonical.Types.p0153 :
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@List.{0} (@Bool)) (@Bool)) (@Body.inc (@List.nil.{0} (@Bool))) (@Prod.mk.{0, 0}
  (@List.{0} (@Bool)) (@Bool) (@List.nil.{0} (@Bool)) (@Bool.true))) := by
  exact @Body.inc.eq_1

-- Independent literal complete proposition: Body.inc.eq_1.
theorem PartACanonical.Surface.m0087 :
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@List.{0} (@Bool)) (@Bool)) (@Body.inc (@List.nil.{0} (@Bool))) (@Prod.mk.{0, 0}
  (@List.{0} (@Bool)) (@Bool) (@List.nil.{0} (@Bool)) (@Bool.true))) := by
  exact @Body.inc.eq_1

-- Independent literal expected type: Body.inc.eq_2.
noncomputable def PartACanonical.Types.p0154 :
(∀ (_v0 : (@List.{0} (@Bool))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@List.{0} (@Bool)) (@Bool)) (@Body.inc (@List.cons.{0} (@Bool) (@Bool.false) _v0))
  (@Prod.mk.{0, 0} (@List.{0} (@Bool)) (@Bool) (@List.cons.{0} (@Bool) (@Bool.true) _v0) (@Bool.false)))) := by
  exact @Body.inc.eq_2

-- Independent literal complete proposition: Body.inc.eq_2.
theorem PartACanonical.Surface.m0088 :
(∀ (_v0 : (@List.{0} (@Bool))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@List.{0} (@Bool)) (@Bool)) (@Body.inc (@List.cons.{0} (@Bool) (@Bool.false) _v0))
  (@Prod.mk.{0, 0} (@List.{0} (@Bool)) (@Bool) (@List.cons.{0} (@Bool) (@Bool.true) _v0) (@Bool.false)))) := by
  exact @Body.inc.eq_2

-- Independent literal expected type: Body.inc.eq_3.
noncomputable def PartACanonical.Types.p0155 :
(∀ (_v0 : (@List.{0} (@Bool))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@List.{0} (@Bool)) (@Bool)) (@Body.inc (@List.cons.{0} (@Bool) (@Bool.true) _v0))
  (@Prod.mk.{0, 0} (@List.{0} (@Bool)) (@Bool) (@List.cons.{0} (@Bool) (@Bool.false) (@Prod.fst.{0, 0} (@List.{0} (@Bool))
  (@Bool) (@Body.inc _v0))) (@Prod.snd.{0, 0} (@List.{0} (@Bool)) (@Bool) (@Body.inc _v0))))) := by
  exact @Body.inc.eq_3

-- Independent literal complete proposition: Body.inc.eq_3.
theorem PartACanonical.Surface.m0089 :
(∀ (_v0 : (@List.{0} (@Bool))),
(@Eq.{(0 + 1)} (@Prod.{0, 0} (@List.{0} (@Bool)) (@Bool)) (@Body.inc (@List.cons.{0} (@Bool) (@Bool.true) _v0))
  (@Prod.mk.{0, 0} (@List.{0} (@Bool)) (@Bool) (@List.cons.{0} (@Bool) (@Bool.false) (@Prod.fst.{0, 0} (@List.{0} (@Bool))
  (@Bool) (@Body.inc _v0))) (@Prod.snd.{0, 0} (@List.{0} (@Bool)) (@Bool) (@Body.inc _v0))))) := by
  exact @Body.inc.eq_3

-- Independent literal expected type: Body.inc_length.
noncomputable def PartACanonical.Types.p0156 :
(∀ (_v0 : (@List.{0} (@Bool))),
(@Eq.{(0 + 1)} (@Nat) (@List.length.{0} (@Bool) (@Prod.fst.{0, 0} (@List.{0} (@Bool)) (@Bool) (@Body.inc _v0)))
  (@List.length.{0} (@Bool) _v0))) := by
  exact @Body.inc_length

-- Independent literal expected type: Body.inc_value.
noncomputable def PartACanonical.Types.p0157 :
(∀ (_v0 : (@List.{0} (@Bool))),
(@Eq.{(0 + 1)} (@Nat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Body.value
  (@Prod.fst.{0, 0} (@List.{0} (@Bool)) (@Bool) (@Body.inc _v0))) (@ite.{(0 + 1)} (@Nat) (@Eq.{(0 + 1)} (@Bool)
  (@Prod.snd.{0, 0} (@List.{0} (@Bool)) (@Bool) (@Body.inc _v0)) (@Bool.true)) (@instDecidableEqBool (@Prod.snd.{0, 0}
  (@List.{0} (@Bool)) (@Bool) (@Body.inc _v0)) (@Bool.true)) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0}
  (@Nat) (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))) (@List.length.{0} (@Bool) _v0)) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))) (@HAdd.hAdd.{0,
  0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Body.value _v0) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat)))))) := by
  exact @Body.inc_value

-- Independent literal expected type: Body.install_exact.
noncomputable def PartACanonical.Types.p0158 :
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
(@Body.install_exact._proof_1 _v0 _v1 _v2 _v3 _v4 _v7 _v8))))) (@Option.none.{0} (@Bool)))),
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
  (@Bool) _v3 (@Bool.false))))))))))))))) := by
  exact @Body.install_exact

-- Independent literal expected type: Body.install_path.
noncomputable def PartACanonical.Types.p0159 :
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
  : Nat)))) _v2))))))))) := by
  exact @Body.install_path

-- Independent literal expected type: Body.installedTape.
noncomputable def PartACanonical.Types.p0160 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ (_v2 : (∀ (_v2 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))),
(@Option.{0} (@Bool)))),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))),
(@Option.{0} (@Bool)))))))) := by
  exact @Body.installedTape

-- Independent literal expected type: Body.installedTape.eq_1.
noncomputable def PartACanonical.Types.p0161 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ (_v2 : (∀ (_v2 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))),
(@Option.{0} (@Bool)))),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Body.installedTape _v0 _v1 _v2 _v3 _v4 _v5) (@ite.{(0 + 1)} (@Option.{0} (@Bool))
  (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v3 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v5)) (@LT.lt.{0}
  (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v5) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 _v4) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@instDecidableAnd (@LT.lt.{0}
  (@Nat) (@instLTNat) _v3 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v5)) (@LT.lt.{0} (@Nat) (@instLTNat)
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v5) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3
  _v4) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Nat.decLt _v3 (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v5)) (@Nat.decLt (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0
  _v1) _v5) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))))) (@Option.some.{0} (@Bool) (@Bool.false)) (@_v2 _v5))))))))) := by
  exact @Body.installedTape.eq_1

-- Independent literal complete proposition: Body.installedTape.eq_1.
theorem PartACanonical.Surface.m0094 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ (_v2 : (∀ (_v2 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))),
(@Option.{0} (@Bool)))),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Body.installedTape _v0 _v1 _v2 _v3 _v4 _v5) (@ite.{(0 + 1)} (@Option.{0} (@Bool))
  (@And (@LT.lt.{0} (@Nat) (@instLTNat) _v3 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v5)) (@LT.lt.{0}
  (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v5) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v3 _v4) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) (@instDecidableAnd (@LT.lt.{0}
  (@Nat) (@instLTNat) _v3 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v5)) (@LT.lt.{0} (@Nat) (@instLTNat)
  (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v5) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3
  _v4) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))))) (@Nat.decLt _v3 (@Fin.val
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v5)) (@Nat.decLt (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0
  _v1) _v5) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 :
  Nat)))))) (@Option.some.{0} (@Bool) (@Bool.false)) (@_v2 _v5))))))))) := by
  exact @Body.installedTape.eq_1

-- Independent literal expected type: Body.iterBits.
noncomputable def PartACanonical.Types.p0162 :
(∀ (_v0 : (@List.{0} (@Bool))),
(∀ (_v1 : (@Nat)),
(@List.{0} (@Bool)))) := by
  exact @Body.iterBits

-- Independent literal expected type: Body.iterBits.eq_1.
noncomputable def PartACanonical.Types.p0163 :
(∀ (_v0 : (@List.{0} (@Bool))),
(@Eq.{(0 + 1)} (@List.{0} (@Bool)) (@Body.iterBits _v0 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  _v0)) := by
  exact @Body.iterBits.eq_1

-- Independent literal complete proposition: Body.iterBits.eq_1.
theorem PartACanonical.Surface.m0095 :
(∀ (_v0 : (@List.{0} (@Bool))),
(@Eq.{(0 + 1)} (@List.{0} (@Bool)) (@Body.iterBits _v0 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  _v0)) := by
  exact @Body.iterBits.eq_1

-- Independent literal expected type: Body.iterBits.eq_2.
noncomputable def PartACanonical.Types.p0164 :
(∀ (_v0 : (@List.{0} (@Bool))),
(∀ (_v1 : (@Nat)),
(@Eq.{(0 + 1)} (@List.{0} (@Bool)) (@Body.iterBits _v0 (@Nat.succ _v1)) (@Body.iterBits (@Prod.fst.{0, 0} (@List.{0}
  (@Bool)) (@Bool) (@Body.inc _v0)) _v1)))) := by
  exact @Body.iterBits.eq_2

-- Independent literal complete proposition: Body.iterBits.eq_2.
theorem PartACanonical.Surface.m0096 :
(∀ (_v0 : (@List.{0} (@Bool))),
(∀ (_v1 : (@Nat)),
(@Eq.{(0 + 1)} (@List.{0} (@Bool)) (@Body.iterBits _v0 (@Nat.succ _v1)) (@Body.iterBits (@Prod.fst.{0, 0} (@List.{0}
  (@Bool)) (@Bool) (@Body.inc _v0)) _v1)))) := by
  exact @Body.iterBits.eq_2

-- Independent literal expected type: Body.iterClock.
noncomputable def PartACanonical.Types.p0165 :
(∀ (_v0 : (@List.{0} (@Bool))),
(∀ (_v1 : (@Nat)),
(@Nat))) := by
  exact @Body.iterClock

-- Independent literal expected type: Body.iterClock.eq_1.
noncomputable def PartACanonical.Types.p0166 :
(∀ (_v0 : (@List.{0} (@Bool))),
(@Eq.{(0 + 1)} (@Nat) (@Body.iterClock _v0 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))) := by
  exact @Body.iterClock.eq_1

-- Independent literal complete proposition: Body.iterClock.eq_1.
theorem PartACanonical.Surface.m0097 :
(∀ (_v0 : (@List.{0} (@Bool))),
(@Eq.{(0 + 1)} (@Nat) (@Body.iterClock _v0 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))
  (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))) := by
  exact @Body.iterClock.eq_1

-- Independent literal expected type: Body.iterClock.eq_2.
noncomputable def PartACanonical.Types.p0167 :
(∀ (_v0 : (@List.{0} (@Bool))),
(∀ (_v1 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@Body.iterClock _v0 (@Nat.succ _v1)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@Body.roundClock _v0) (@Body.iterClock (@Prod.fst.{0, 0} (@List.{0} (@Bool)) (@Bool) (@Body.inc
  _v0)) _v1))))) := by
  exact @Body.iterClock.eq_2

-- Independent literal complete proposition: Body.iterClock.eq_2.
theorem PartACanonical.Surface.m0098 :
(∀ (_v0 : (@List.{0} (@Bool))),
(∀ (_v1 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@Body.iterClock _v0 (@Nat.succ _v1)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@Body.roundClock _v0) (@Body.iterClock (@Prod.fst.{0, 0} (@List.{0} (@Bool)) (@Bool) (@Body.inc
  _v0)) _v1))))) := by
  exact @Body.iterClock.eq_2

-- Independent literal expected type: Body.iter_clock_le.
noncomputable def PartACanonical.Types.p0168 :
(∀ (_v0 : (@List.{0} (@Bool))),
(∀ (_v1 : (@Nat)),
(@LE.le.{0} (@Nat) (@instLENat) (@Body.iterClock _v0 _v1) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) _v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) (@List.length.{0} (@Bool) _v0)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 :
  Nat)))))))) := by
  exact @Body.iter_clock_le

-- Independent literal expected type: Body.iter_length.
noncomputable def PartACanonical.Types.p0169 :
(∀ (_v0 : (@List.{0} (@Bool))),
(∀ (_v1 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@List.length.{0} (@Bool) (@Body.iterBits _v0 _v1)) (@List.length.{0} (@Bool) _v0)))) := by
  exact @Body.iter_length

-- Independent literal expected type: Body.machine.
noncomputable def PartACanonical.Types.p0170 :
(@Pnp3.Complexity.Uniform.V1.UniformTM) := by
  exact @Body.machine

-- Independent literal expected type: Body.put.
noncomputable def PartACanonical.Types.p0171 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Option.{0} (@Bool))),
(∀ (_v3 : (@Nat)),
(@Option.{0} (@Bool)))))) := by
  exact @Body.put

-- Independent literal expected type: Body.put.eq_1.
noncomputable def PartACanonical.Types.p0172 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Option.{0} (@Bool))),
(∀ (_v3 : (@Nat)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Body.put _v0 _v1 _v2 _v3) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)}
  (@Nat) _v3 _v1) (@instDecidableEqNat _v3 _v1) _v2 (@_v0 _v3))))))) := by
  exact @Body.put.eq_1

-- Independent literal complete proposition: Body.put.eq_1.
theorem PartACanonical.Surface.m0101 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Option.{0} (@Bool))),
(∀ (_v3 : (@Nat)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Body.put _v0 _v1 _v2 _v3) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 + 1)}
  (@Nat) _v3 _v1) (@instDecidableEqNat _v3 _v1) _v2 (@_v0 _v3))))))) := by
  exact @Body.put.eq_1

-- Independent literal expected type: Body.put_same.
noncomputable def PartACanonical.Types.p0173 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(@Eq.{(0 + 1)} (∀ (_v2 : (@Nat)),
(@Option.{0} (@Bool))) (@Body.put _v0 _v1 (@_v0 _v1)) _v0))) := by
  exact @Body.put_same

-- Independent literal expected type: Body.q.
noncomputable def PartACanonical.Types.p0174 :
(∀ (_v0 : (@Nat)),
(@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))))) := by
  exact @Body.q

-- Independent literal expected type: Body.raw.
noncomputable def PartACanonical.Types.p0175 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat))))),
(∀ (_v1 : (@Option.{0} (@Bool))),
(@Prod.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (9 : Nat) (@instOfNatNat (9 : Nat)))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))))) := by
  exact @Body.raw

-- Independent literal expected type: Body.rawMachine.
noncomputable def PartACanonical.Types.p0176 :
(@Pnp3.Complexity.Uniform.V1.UniformTM) := by
  exact @Body.rawMachine

-- Independent literal expected type: Body.raw_counter_parsed.
noncomputable def PartACanonical.Types.p0177 :
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
  (@Body.machine) (@Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength _v1 _v2) _v9 _v16 _v15))))))))))))))))))))))))))))) := by
  exact @Body.raw_counter_parsed

-- Independent literal expected type: Body.raw_repeated_parsed.
noncomputable def PartACanonical.Types.p0178 :
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
  _v9) _v16) _v18))))))))))))))))))))))))))))))) := by
  exact @Body.raw_repeated_parsed

-- Independent literal expected type: Body.raw_source_after_header.
noncomputable def PartACanonical.Types.p0179 :
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
  _v2) _v10) _v12))))))))))))))))) := by
  exact @Body.raw_source_after_header

-- Independent literal expected type: Body.reads_cons.
noncomputable def PartACanonical.Types.p0180 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Bool)),
(∀ (_v3 : (@List.{0} (@Bool))),
(@Iff (@Body.Reads _v0 _v1 (@List.cons.{0} (@Bool) _v2 _v3)) (@And (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@_v0
  (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 (@List.length.{0} (@Bool) _v3)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat)
  (@instOfNatNat (1 : Nat))))) (@Option.some.{0} (@Bool) _v2)) (@Body.Reads _v0 _v1 _v3))))))) := by
  exact @Body.reads_cons

-- Independent literal expected type: Body.reads_put_outside.
noncomputable def PartACanonical.Types.p0181 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@List.{0} (@Bool))),
(∀ (_v3 : (@Body.Reads _v0 _v1 _v2)),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@Option.{0} (@Bool))),
(∀ (_v6 : (@LT.lt.{0} (@Nat) (@instLTNat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) _v1 (@List.length.{0} (@Bool) _v2)) _v4)),
(@Body.Reads (@Body.put _v0 _v4 _v5) _v1 _v2)))))))) := by
  exact @Body.reads_put_outside

-- Independent literal expected type: Body.repeated_exact.
noncomputable def PartACanonical.Types.p0182 :
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
  _v12))))))))))))))))))) := by
  exact @Body.repeated_exact

-- Independent literal expected type: Body.roundClock.
noncomputable def PartACanonical.Types.p0183 :
(∀ (_v0 : (@List.{0} (@Bool))),
(@Nat)) := by
  exact @Body.roundClock

-- Independent literal expected type: Body.roundClock.eq_1.
noncomputable def PartACanonical.Types.p0184 :
(∀ (_v0 : (@List.{0} (@Bool))),
(@Eq.{(0 + 1)} (@Nat) (@Body.roundClock _v0) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@Body.carryClock _v0 (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))))) := by
  exact @Body.roundClock.eq_1

-- Independent literal complete proposition: Body.roundClock.eq_1.
theorem PartACanonical.Surface.m0109 :
(∀ (_v0 : (@List.{0} (@Bool))),
(@Eq.{(0 + 1)} (@Nat) (@Body.roundClock _v0) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@Body.carryClock _v0 (@OfNat.ofNat.{0}
  (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))))))) := by
  exact @Body.roundClock.eq_1

-- Independent literal expected type: Body.round_clock_le.
noncomputable def PartACanonical.Types.p0185 :
(∀ (_v0 : (@List.{0} (@Bool))),
(@LE.le.{0} (@Nat) (@instLENat) (@Body.roundClock _v0) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat)
  (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat)
  (2 : Nat) (@instOfNatNat (2 : Nat))) (@List.length.{0} (@Bool) _v0)) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat
  (3 : Nat)))))) := by
  exact @Body.round_clock_le

-- Independent literal expected type: Body.round_exact.
noncomputable def PartACanonical.Types.p0186 :
(@Body.Target.Round) := by
  exact @Body.round_exact

-- Independent literal expected type: Body.round_path.
noncomputable def PartACanonical.Types.p0187 :
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
  _v2))))))))) := by
  exact @Body.round_path

-- Independent literal expected type: Body.seed_path.
noncomputable def PartACanonical.Types.p0188 :
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

-- Independent literal expected type: Body.sweep.
noncomputable def PartACanonical.Types.p0189 :
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

-- Independent literal expected type: Body.value.
noncomputable def PartACanonical.Types.p0190 :
(∀ (_v0 : (@List.{0} (@Bool))),
(@Nat)) := by
  exact @Body.value

-- Independent literal expected type: Body.value.eq_1.
noncomputable def PartACanonical.Types.p0191 :
(@Eq.{(0 + 1)} (@Nat) (@Body.value (@List.nil.{0} (@Bool))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat)))) := by
  exact @Body.value.eq_1

-- Independent literal complete proposition: Body.value.eq_1.
theorem PartACanonical.Surface.m0115 :
(@Eq.{(0 + 1)} (@Nat) (@Body.value (@List.nil.{0} (@Bool))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 :
  Nat)))) := by
  exact @Body.value.eq_1

-- Independent literal expected type: Body.value.eq_2.
noncomputable def PartACanonical.Types.p0192 :
(∀ (_v0 : (@Bool)),
(∀ (_v1 : (@List.{0} (@Bool))),
(@Eq.{(0 + 1)} (@Nat) (@Body.value (@List.cons.{0} (@Bool) _v0 _v1)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@Bool.toNat _v0) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@Body.value _v1)))))) := by
  exact @Body.value.eq_2

-- Independent literal complete proposition: Body.value.eq_2.
theorem PartACanonical.Surface.m0116 :
(∀ (_v0 : (@Bool)),
(∀ (_v1 : (@List.{0} (@Bool))),
(@Eq.{(0 + 1)} (@Nat) (@Body.value (@List.cons.{0} (@Bool) _v0 _v1)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat)
  (@instHAdd.{0} (@Nat) (@instAddNat)) (@Bool.toNat _v0) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat)
  (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) (@Body.value _v1)))))) := by
  exact @Body.value.eq_2

-- Independent literal expected type: Body.value_lt.
noncomputable def PartACanonical.Types.p0193 :
(∀ (_v0 : (@List.{0} (@Bool))),
(@LT.lt.{0} (@Nat) (@instLTNat) (@Body.value _v0) (@HPow.hPow.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHPow.{0, 0} (@Nat)
  (@Nat) (@Monoid.toNatPow.{0} (@Nat) (@Nat.instMonoid))) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  (@List.length.{0} (@Bool) _v0)))) := by
  exact @Body.value_lt

-- Independent literal expected type: Body.zero_value.
noncomputable def PartACanonical.Types.p0194 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@Body.value (@List.replicate.{0} (@Bool) _v0 (@Bool.false))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat))))) := by
  exact @Body.zero_value
