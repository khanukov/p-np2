import Tests.PartAR1LiteralPilot

set_option autoImplicit false

-- Independent literal expected type: ConnectedRead.Exact.
noncomputable def PartACanonical.Types.p0314 :
(∀ (_v0 : (@Nat)),
(Sort 0)) := by
  exact @ConnectedRead.Exact

-- Independent literal expected type: ConnectedRead.exact.
noncomputable def PartACanonical.Types.p0315 :
(∀ (_v0 : (@Nat)),
(@ConnectedRead.Exact _v0)) := by
  exact @ConnectedRead.exact

-- Independent literal expected type: GammaSupport.Exact.
noncomputable def PartACanonical.Types.p0395 :
(Sort 0) := by
  exact @GammaSupport.Exact

-- Independent literal expected type: GammaSupport.canonical.
noncomputable def PartACanonical.Types.p0396 :
(∀ (_v0 : (@Nat)),
(∀ {_v1 : (@Nat)},
(∀ (_v2 : (@Pnp4.Frontier.ContractExpansion.PrefixBitVec _v1)),
(∀ {_v3 : (@Sigma.{0, 0} (@Nat) (fun (_v3 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v3))))},
(∀ (_v4 : (@Eq.{(0 + 1)} (@Option.{0} (@Sigma.{0, 0} (@Nat) (fun (_v4 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v4))))) (@Pnp4.Frontier.ContractExpansion.contentInput?
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v1 _v2) (@Option.some.{0} (@Sigma.{0, 0} (@Nat) (fun (_v4 :
  (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v4)))) _v3))),
(∀ (_v5 : (@Eq.{(0 + 1)} (@Bool) (@Pnp4.Frontier.ContractExpansion.contentSemanticAccepts
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v1 _v2) (@Bool.true))),
(∀ (_v6 : (@LE.le.{0} (@Nat) (@instLENat) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))
  (@Pnp4.Frontier.ContractExpansion.PrefixInput.n (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) (@Sigma.fst.{0, 0} (@Nat) (fun (_v6 : (@Nat)) =>
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v6))) _v3)))),
(@LE.le.{0} (@Nat) (@instLENat) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat))
  (@Pnp4.Frontier.ContractExpansion.tagLen) (@Pnp4.Frontier.ContractExpansion.gammaLen
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v7))) _v3)) (@Sigma.snd.{0, 0} (@Nat) (fun (_v7 : (@Nat)) =>
(@Pnp4.Frontier.ContractExpansion.PrefixInput (@Pnp4.Frontier.treeMCSPSearchProblem
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)))) (@Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0) (@Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v7))) _v3)))) _v1)))))))) := by
  exact @GammaSupport.canonical

-- Independent literal expected type: GammaSupport.exact.
noncomputable def PartACanonical.Types.p0397 :
(@GammaSupport.Exact) := by
  exact @GammaSupport.exact

-- Independent literal expected type: InputRead.Edge.
noncomputable def PartACanonical.Types.p0425 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@InputRead.Node)),
(∀ (_v2 : (@InputRead.Node)),
(Sort 0)))) := by
  exact @InputRead.Edge

-- Independent literal expected type: InputRead.Edge.after.
noncomputable def PartACanonical.Types.p0426 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@InputRead.Node)},
(∀ {_v2 : (@InputRead.Node)},
(∀ (_v3 : (@InputRead.Edge _v0 _v1 _v2)),
(@LE.le.{0} (@Nat) (@instLENat) (@InputRead.Node.head _v2) _v0))))) := by
  exact @InputRead.Edge.after

-- Independent literal expected type: InputRead.Edge.before.
noncomputable def PartACanonical.Types.p0427 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@InputRead.Node)},
(∀ {_v2 : (@InputRead.Node)},
(∀ (_v3 : (@InputRead.Edge _v0 _v1 _v2)),
(@LE.le.{0} (@Nat) (@instLENat) (@InputRead.Node.head _v1) _v0))))) := by
  exact @InputRead.Edge.before

-- Independent literal expected type: InputRead.Edge.casesOn.
noncomputable def PartACanonical.Types.p0428.{u} :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@InputRead.Node)},
(∀ {_v2 : (@InputRead.Node)},
(∀ {_v3 : (∀ (_v3 : (@InputRead.Edge _v0 _v1 _v2)),
(Sort u))},
(∀ (_v4 : (@InputRead.Edge _v0 _v1 _v2)),
(∀ (_v5 : (∀ (_v5 : (@LE.le.{0} (@Nat) (@instLENat) (@InputRead.Node.head _v1) _v0)),
(∀ (_v6 : (@LE.le.{0} (@Nat) (@instLENat) (@InputRead.Node.head _v2) _v0)),
(∀ (_v7 : (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@InputRead.machine))) (@Prod.fst.{0,
  0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@InputRead.machine))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@InputRead.machine)
  (@InputRead.Node.state _v1) (@InputRead.Node.tape _v1 (@InputRead.Node.head _v1)))) (@InputRead.Node.state _v2))),
(∀ (_v8 : (@Eq.{(0 + 1)} (@Nat) (@InputRead.dest (@InputRead.Node.head _v1) (@Prod.snd.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move) (@Prod.snd.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@InputRead.machine))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@InputRead.machine) (@InputRead.Node.state _v1) (@InputRead.Node.tape _v1
  (@InputRead.Node.head _v1)))))) (@InputRead.Node.head _v2))),
(∀ (_v9 : (@Eq.{(0 + 1)} (∀ (_v9 : (@Nat)),
(@Option.{0} (@Bool))) (@InputRead.Node.tape _v2) (@InputRead.put (@InputRead.Node.tape _v1) (@InputRead.Node.head _v1)
  (@Prod.fst.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Prod.snd.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@InputRead.machine))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@InputRead.machine)
  (@InputRead.Node.state _v1) (@InputRead.Node.tape _v1 (@InputRead.Node.head _v1)))))))),
(@_v3 (@InputRead.Edge.mk _v0 _v1 _v2 _v5 _v6 _v7 _v8 _v9)))))))),
(@_v3 _v4))))))) := by
  exact @InputRead.Edge.casesOn.{u}

-- Independent literal expected type: InputRead.Edge.mk.
noncomputable def PartACanonical.Types.p0429 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@InputRead.Node)},
(∀ {_v2 : (@InputRead.Node)},
(∀ (_v3 : (@LE.le.{0} (@Nat) (@instLENat) (@InputRead.Node.head _v1) _v0)),
(∀ (_v4 : (@LE.le.{0} (@Nat) (@instLENat) (@InputRead.Node.head _v2) _v0)),
(∀ (_v5 : (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@InputRead.machine))) (@Prod.fst.{0,
  0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@InputRead.machine))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@InputRead.machine)
  (@InputRead.Node.state _v1) (@InputRead.Node.tape _v1 (@InputRead.Node.head _v1)))) (@InputRead.Node.state _v2))),
(∀ (_v6 : (@Eq.{(0 + 1)} (@Nat) (@InputRead.dest (@InputRead.Node.head _v1) (@Prod.snd.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move) (@Prod.snd.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@InputRead.machine))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@InputRead.machine) (@InputRead.Node.state _v1) (@InputRead.Node.tape _v1
  (@InputRead.Node.head _v1)))))) (@InputRead.Node.head _v2))),
(∀ (_v7 : (@Eq.{(0 + 1)} (∀ (_v7 : (@Nat)),
(@Option.{0} (@Bool))) (@InputRead.Node.tape _v2) (@InputRead.put (@InputRead.Node.tape _v1) (@InputRead.Node.head _v1)
  (@Prod.fst.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Prod.snd.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@InputRead.machine))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@InputRead.machine)
  (@InputRead.Node.state _v1) (@InputRead.Node.tape _v1 (@InputRead.Node.head _v1)))))))),
(@InputRead.Edge _v0 _v1 _v2))))))))) := by
  exact @InputRead.Edge.mk

-- Independent literal expected type: InputRead.Edge.move.
noncomputable def PartACanonical.Types.p0430 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@InputRead.Node)},
(∀ {_v2 : (@InputRead.Node)},
(∀ (_v3 : (@InputRead.Edge _v0 _v1 _v2)),
(@Eq.{(0 + 1)} (@Nat) (@InputRead.dest (@InputRead.Node.head _v1) (@Prod.snd.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move) (@Prod.snd.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@InputRead.machine))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@InputRead.machine) (@InputRead.Node.state _v1) (@InputRead.Node.tape _v1
  (@InputRead.Node.head _v1)))))) (@InputRead.Node.head _v2)))))) := by
  exact @InputRead.Edge.move

-- Independent literal expected type: InputRead.Edge.noConfusion.
noncomputable def PartACanonical.Types.p0431.{u} :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@InputRead.Node)},
(∀ {_v2 : (@InputRead.Node)},
(∀ {_v3 : (Sort u)},
(∀ {_v4 : (@InputRead.Edge _v0 _v1 _v2)},
(∀ {_v5 : (@InputRead.Edge _v0 _v1 _v2)},
(∀ (_v6 : (@Eq.{0} (@InputRead.Edge _v0 _v1 _v2) _v4 _v5)),
(@InputRead.Edge.noConfusionType.{u} _v0 _v1 _v2 _v3 _v4 _v5)))))))) := by
  exact @InputRead.Edge.noConfusion.{u}

-- Independent literal expected type: InputRead.Edge.noConfusionType.
noncomputable def PartACanonical.Types.p0432.{u} :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@InputRead.Node)},
(∀ {_v2 : (@InputRead.Node)},
(∀ (_v3 : (Sort u)),
(∀ (_v4 : (@InputRead.Edge _v0 _v1 _v2)),
(∀ (_v5 : (@InputRead.Edge _v0 _v1 _v2)),
(Sort u))))))) := by
  exact @InputRead.Edge.noConfusionType.{u}

-- Independent literal expected type: InputRead.Edge.noConfusionType.withCtor.
noncomputable def PartACanonical.Types.p0433.{u} :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@InputRead.Node)),
(∀ (_v2 : (@InputRead.Node)),
(∀ (_v3 : (Sort (u + 1))),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (@InputRead.Edge.noConfusionType.withCtorType.{u} _v0 _v1 _v2 _v3 _v4)),
(∀ (_v6 : _v3),
(∀ (_v7 : (@InputRead.Edge _v0 _v1 _v2)),
_v3)))))))) := by
  exact @InputRead.Edge.noConfusionType.withCtor.{u}

-- Independent literal expected type: InputRead.Edge.noConfusionType.withCtorType.
noncomputable def PartACanonical.Types.p0434.{u} :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@InputRead.Node)),
(∀ (_v2 : (@InputRead.Node)),
(∀ (_v3 : (Sort (u + 1))),
(∀ (_v4 : (@Nat)),
(Sort (u + 1))))))) := by
  exact @InputRead.Edge.noConfusionType.withCtorType.{u}

-- Independent literal expected type: InputRead.Edge.rec.
noncomputable def PartACanonical.Types.p0435.{u} :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@InputRead.Node)},
(∀ {_v2 : (@InputRead.Node)},
(∀ {_v3 : (∀ (_v3 : (@InputRead.Edge _v0 _v1 _v2)),
(Sort u))},
(∀ (_v4 : (∀ (_v4 : (@LE.le.{0} (@Nat) (@instLENat) (@InputRead.Node.head _v1) _v0)),
(∀ (_v5 : (@LE.le.{0} (@Nat) (@instLENat) (@InputRead.Node.head _v2) _v0)),
(∀ (_v6 : (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@InputRead.machine))) (@Prod.fst.{0,
  0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@InputRead.machine))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@InputRead.machine)
  (@InputRead.Node.state _v1) (@InputRead.Node.tape _v1 (@InputRead.Node.head _v1)))) (@InputRead.Node.state _v2))),
(∀ (_v7 : (@Eq.{(0 + 1)} (@Nat) (@InputRead.dest (@InputRead.Node.head _v1) (@Prod.snd.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move) (@Prod.snd.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@InputRead.machine))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@InputRead.machine) (@InputRead.Node.state _v1) (@InputRead.Node.tape _v1
  (@InputRead.Node.head _v1)))))) (@InputRead.Node.head _v2))),
(∀ (_v8 : (@Eq.{(0 + 1)} (∀ (_v8 : (@Nat)),
(@Option.{0} (@Bool))) (@InputRead.Node.tape _v2) (@InputRead.put (@InputRead.Node.tape _v1) (@InputRead.Node.head _v1)
  (@Prod.fst.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Prod.snd.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@InputRead.machine))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@InputRead.machine)
  (@InputRead.Node.state _v1) (@InputRead.Node.tape _v1 (@InputRead.Node.head _v1)))))))),
(@_v3 (@InputRead.Edge.mk _v0 _v1 _v2 _v4 _v5 _v6 _v7 _v8)))))))),
(∀ (_v5 : (@InputRead.Edge _v0 _v1 _v2)),
(@_v3 _v5))))))) := by
  exact @InputRead.Edge.rec.{u}

-- Independent literal expected type: InputRead.Edge.recOn.
noncomputable def PartACanonical.Types.p0436.{u} :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@InputRead.Node)},
(∀ {_v2 : (@InputRead.Node)},
(∀ {_v3 : (∀ (_v3 : (@InputRead.Edge _v0 _v1 _v2)),
(Sort u))},
(∀ (_v4 : (@InputRead.Edge _v0 _v1 _v2)),
(∀ (_v5 : (∀ (_v5 : (@LE.le.{0} (@Nat) (@instLENat) (@InputRead.Node.head _v1) _v0)),
(∀ (_v6 : (@LE.le.{0} (@Nat) (@instLENat) (@InputRead.Node.head _v2) _v0)),
(∀ (_v7 : (@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@InputRead.machine))) (@Prod.fst.{0,
  0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@InputRead.machine))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@InputRead.machine)
  (@InputRead.Node.state _v1) (@InputRead.Node.tape _v1 (@InputRead.Node.head _v1)))) (@InputRead.Node.state _v2))),
(∀ (_v8 : (@Eq.{(0 + 1)} (@Nat) (@InputRead.dest (@InputRead.Node.head _v1) (@Prod.snd.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move) (@Prod.snd.{0, 0} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount
  (@InputRead.machine))) (@Prod.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move))
  (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@InputRead.machine) (@InputRead.Node.state _v1) (@InputRead.Node.tape _v1
  (@InputRead.Node.head _v1)))))) (@InputRead.Node.head _v2))),
(∀ (_v9 : (@Eq.{(0 + 1)} (∀ (_v9 : (@Nat)),
(@Option.{0} (@Bool))) (@InputRead.Node.tape _v2) (@InputRead.put (@InputRead.Node.tape _v1) (@InputRead.Node.head _v1)
  (@Prod.fst.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Prod.snd.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@InputRead.machine))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@InputRead.machine)
  (@InputRead.Node.state _v1) (@InputRead.Node.tape _v1 (@InputRead.Node.head _v1)))))))),
(@_v3 (@InputRead.Edge.mk _v0 _v1 _v2 _v5 _v6 _v7 _v8 _v9)))))))),
(@_v3 _v4))))))) := by
  exact @InputRead.Edge.recOn.{u}

-- Independent literal expected type: InputRead.Edge.row.
noncomputable def PartACanonical.Types.p0437 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@InputRead.Node)},
(∀ {_v2 : (@InputRead.Node)},
(∀ (_v3 : (@InputRead.Edge _v0 _v1 _v2)),
(@Eq.{(0 + 1)} (@Fin (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@InputRead.machine))) (@Prod.fst.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@InputRead.machine))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@InputRead.machine)
  (@InputRead.Node.state _v1) (@InputRead.Node.tape _v1 (@InputRead.Node.head _v1)))) (@InputRead.Node.state _v2)))))) := by
  exact @InputRead.Edge.row

-- Independent literal expected type: InputRead.Edge.tape.
noncomputable def PartACanonical.Types.p0438 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@InputRead.Node)},
(∀ {_v2 : (@InputRead.Node)},
(∀ (_v3 : (@InputRead.Edge _v0 _v1 _v2)),
(@Eq.{(0 + 1)} (∀ (_v4 : (@Nat)),
(@Option.{0} (@Bool))) (@InputRead.Node.tape _v2) (@InputRead.put (@InputRead.Node.tape _v1) (@InputRead.Node.head _v1)
  (@Prod.fst.{0, 0} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move) (@Prod.snd.{0, 0} (@Fin
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@InputRead.machine))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move)) (@Pnp3.Complexity.Uniform.V1.UniformTM.step (@InputRead.machine)
  (@InputRead.Node.state _v1) (@InputRead.Node.tape _v1 (@InputRead.Node.head _v1))))))))))) := by
  exact @InputRead.Edge.tape

-- Independent literal expected type: InputRead.Node.
noncomputable def PartACanonical.Types.p0439 :
(Sort (0 + 1)) := by
  exact @InputRead.Node

-- Independent literal expected type: InputRead.Node.casesOn.
noncomputable def PartACanonical.Types.p0440.{u} :
(∀ {_v0 : (∀ (_v0 : (@InputRead.Node)),
(Sort u))},
(∀ (_v1 : (@InputRead.Node)),
(∀ (_v2 : (∀ (_v2 : (@Fin (@OfNat.ofNat.{0} (@Nat) (41 : Nat) (@instOfNatNat (41 : Nat))))),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (∀ (_v4 : (@Nat)),
(@Option.{0} (@Bool)))),
(@_v0 (@InputRead.Node.mk _v2 _v3 _v4)))))),
(@_v0 _v1)))) := by
  exact @InputRead.Node.casesOn.{u}

-- Independent literal expected type: InputRead.Node.head.
noncomputable def PartACanonical.Types.p0441 :
(∀ (_v0 : (@InputRead.Node)),
(@Nat)) := by
  exact @InputRead.Node.head

-- Independent literal expected type: InputRead.Node.mk.
noncomputable def PartACanonical.Types.p0442 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (41 : Nat) (@instOfNatNat (41 : Nat))))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (∀ (_v2 : (@Nat)),
(@Option.{0} (@Bool)))),
(@InputRead.Node)))) := by
  exact @InputRead.Node.mk

-- Independent literal expected type: InputRead.Node.mk.inj.
noncomputable def PartACanonical.Types.p0443 :
(∀ {_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (41 : Nat) (@instOfNatNat (41 : Nat))))},
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (∀ (_v2 : (@Nat)),
(@Option.{0} (@Bool)))},
(∀ {_v3 : (@Fin (@OfNat.ofNat.{0} (@Nat) (41 : Nat) (@instOfNatNat (41 : Nat))))},
(∀ {_v4 : (@Nat)},
(∀ {_v5 : (∀ (_v5 : (@Nat)),
(@Option.{0} (@Bool)))},
(∀ (_v6 : (@Eq.{(0 + 1)} (@InputRead.Node) (@InputRead.Node.mk _v0 _v1 _v2) (@InputRead.Node.mk _v3 _v4 _v5))),
(@And (@Eq.{(0 + 1)} (@Fin (@OfNat.ofNat.{0} (@Nat) (41 : Nat) (@instOfNatNat (41 : Nat)))) _v0 _v3) (@And (@Eq.{(0 +
  1)} (@Nat) _v1 _v4) (@Eq.{(0 + 1)} (∀ (_v7 : (@Nat)),
(@Option.{0} (@Bool))) _v2 _v5)))))))))) := by
  exact @InputRead.Node.mk.inj

-- Independent literal complete proposition: InputRead.Node.mk.inj.
theorem PartACanonical.Surface.m0266 :
(∀ {_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (41 : Nat) (@instOfNatNat (41 : Nat))))},
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (∀ (_v2 : (@Nat)),
(@Option.{0} (@Bool)))},
(∀ {_v3 : (@Fin (@OfNat.ofNat.{0} (@Nat) (41 : Nat) (@instOfNatNat (41 : Nat))))},
(∀ {_v4 : (@Nat)},
(∀ {_v5 : (∀ (_v5 : (@Nat)),
(@Option.{0} (@Bool)))},
(∀ (_v6 : (@Eq.{(0 + 1)} (@InputRead.Node) (@InputRead.Node.mk _v0 _v1 _v2) (@InputRead.Node.mk _v3 _v4 _v5))),
(@And (@Eq.{(0 + 1)} (@Fin (@OfNat.ofNat.{0} (@Nat) (41 : Nat) (@instOfNatNat (41 : Nat)))) _v0 _v3) (@And (@Eq.{(0 +
  1)} (@Nat) _v1 _v4) (@Eq.{(0 + 1)} (∀ (_v7 : (@Nat)),
(@Option.{0} (@Bool))) _v2 _v5)))))))))) := by
  exact @InputRead.Node.mk.inj

-- Independent literal expected type: InputRead.Node.mk.injEq.
noncomputable def PartACanonical.Types.p0444 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (41 : Nat) (@instOfNatNat (41 : Nat))))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (∀ (_v2 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v3 : (@Fin (@OfNat.ofNat.{0} (@Nat) (41 : Nat) (@instOfNatNat (41 : Nat))))),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (∀ (_v5 : (@Nat)),
(@Option.{0} (@Bool)))),
(@Eq.{(0 + 1)} (Sort 0) (@Eq.{(0 + 1)} (@InputRead.Node) (@InputRead.Node.mk _v0 _v1 _v2) (@InputRead.Node.mk _v3 _v4
  _v5)) (@And (@Eq.{(0 + 1)} (@Fin (@OfNat.ofNat.{0} (@Nat) (41 : Nat) (@instOfNatNat (41 : Nat)))) _v0 _v3) (@And
  (@Eq.{(0 + 1)} (@Nat) _v1 _v4) (@Eq.{(0 + 1)} (∀ (_v6 : (@Nat)),
(@Option.{0} (@Bool))) _v2 _v5)))))))))) := by
  exact @InputRead.Node.mk.injEq

-- Independent literal complete proposition: InputRead.Node.mk.injEq.
theorem PartACanonical.Surface.m0267 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (41 : Nat) (@instOfNatNat (41 : Nat))))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (∀ (_v2 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v3 : (@Fin (@OfNat.ofNat.{0} (@Nat) (41 : Nat) (@instOfNatNat (41 : Nat))))),
(∀ (_v4 : (@Nat)),
(∀ (_v5 : (∀ (_v5 : (@Nat)),
(@Option.{0} (@Bool)))),
(@Eq.{(0 + 1)} (Sort 0) (@Eq.{(0 + 1)} (@InputRead.Node) (@InputRead.Node.mk _v0 _v1 _v2) (@InputRead.Node.mk _v3 _v4
  _v5)) (@And (@Eq.{(0 + 1)} (@Fin (@OfNat.ofNat.{0} (@Nat) (41 : Nat) (@instOfNatNat (41 : Nat)))) _v0 _v3) (@And
  (@Eq.{(0 + 1)} (@Nat) _v1 _v4) (@Eq.{(0 + 1)} (∀ (_v6 : (@Nat)),
(@Option.{0} (@Bool))) _v2 _v5)))))))))) := by
  exact @InputRead.Node.mk.injEq

-- Independent literal expected type: InputRead.Node.mk.sizeOf_spec.
noncomputable def PartACanonical.Types.p0445 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (41 : Nat) (@instOfNatNat (41 : Nat))))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (∀ (_v2 : (@Nat)),
(@Option.{0} (@Bool)))),
(@Eq.{(0 + 1)} (@Nat) (@SizeOf.sizeOf.{(0 + 1)} (@InputRead.Node) (@InputRead.Node._sizeOf_inst) (@InputRead.Node.mk _v0
  _v1 _v2)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))
  (@SizeOf.sizeOf.{(0 + 1)} (@Fin (@OfNat.ofNat.{0} (@Nat) (41 : Nat) (@instOfNatNat (41 : Nat)))) (@Fin._sizeOf_inst
  (@OfNat.ofNat.{0} (@Nat) (41 : Nat) (@instOfNatNat (41 : Nat)))) _v0)) (@SizeOf.sizeOf.{(0 + 1)} (@Nat) (@instSizeOfNat)
  _v1)))))) := by
  exact @InputRead.Node.mk.sizeOf_spec

-- Independent literal complete proposition: InputRead.Node.mk.sizeOf_spec.
theorem PartACanonical.Surface.m0268 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (41 : Nat) (@instOfNatNat (41 : Nat))))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (∀ (_v2 : (@Nat)),
(@Option.{0} (@Bool)))),
(@Eq.{(0 + 1)} (@Nat) (@SizeOf.sizeOf.{(0 + 1)} (@InputRead.Node) (@InputRead.Node._sizeOf_inst) (@InputRead.Node.mk _v0
  _v1 _v2)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))
  (@SizeOf.sizeOf.{(0 + 1)} (@Fin (@OfNat.ofNat.{0} (@Nat) (41 : Nat) (@instOfNatNat (41 : Nat)))) (@Fin._sizeOf_inst
  (@OfNat.ofNat.{0} (@Nat) (41 : Nat) (@instOfNatNat (41 : Nat)))) _v0)) (@SizeOf.sizeOf.{(0 + 1)} (@Nat) (@instSizeOfNat)
  _v1)))))) := by
  exact @InputRead.Node.mk.sizeOf_spec

-- Independent literal expected type: InputRead.Node.noConfusion.
noncomputable def PartACanonical.Types.p0446.{u} :
(∀ {_v0 : (Sort u)},
(∀ {_v1 : (@InputRead.Node)},
(∀ {_v2 : (@InputRead.Node)},
(∀ (_v3 : (@Eq.{(0 + 1)} (@InputRead.Node) _v1 _v2)),
(@InputRead.Node.noConfusionType.{u} _v0 _v1 _v2))))) := by
  exact @InputRead.Node.noConfusion.{u}

-- Independent literal expected type: InputRead.Node.noConfusionType.
noncomputable def PartACanonical.Types.p0447.{u} :
(∀ (_v0 : (Sort u)),
(∀ (_v1 : (@InputRead.Node)),
(∀ (_v2 : (@InputRead.Node)),
(Sort u)))) := by
  exact @InputRead.Node.noConfusionType.{u}

-- Independent literal expected type: InputRead.Node.noConfusionType.withCtor.
noncomputable def PartACanonical.Types.p0448.{u} :
(∀ (_v0 : (Sort (u + 1))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@InputRead.Node.noConfusionType.withCtorType.{u} _v0 _v1)),
(∀ (_v3 : _v0),
(∀ (_v4 : (@InputRead.Node)),
_v0))))) := by
  exact @InputRead.Node.noConfusionType.withCtor.{u}

-- Independent literal expected type: InputRead.Node.noConfusionType.withCtorType.
noncomputable def PartACanonical.Types.p0449.{u} :
(∀ (_v0 : (Sort (u + 1))),
(∀ (_v1 : (@Nat)),
(Sort (max ((0 + 1) + 1) (u + 1))))) := by
  exact @InputRead.Node.noConfusionType.withCtorType.{u}

-- Independent literal expected type: InputRead.Node.rec.
noncomputable def PartACanonical.Types.p0450.{u} :
(∀ {_v0 : (∀ (_v0 : (@InputRead.Node)),
(Sort u))},
(∀ (_v1 : (∀ (_v1 : (@Fin (@OfNat.ofNat.{0} (@Nat) (41 : Nat) (@instOfNatNat (41 : Nat))))),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (∀ (_v3 : (@Nat)),
(@Option.{0} (@Bool)))),
(@_v0 (@InputRead.Node.mk _v1 _v2 _v3)))))),
(∀ (_v2 : (@InputRead.Node)),
(@_v0 _v2)))) := by
  exact @InputRead.Node.rec.{u}

-- Independent literal expected type: InputRead.Node.recOn.
noncomputable def PartACanonical.Types.p0451.{u} :
(∀ {_v0 : (∀ (_v0 : (@InputRead.Node)),
(Sort u))},
(∀ (_v1 : (@InputRead.Node)),
(∀ (_v2 : (∀ (_v2 : (@Fin (@OfNat.ofNat.{0} (@Nat) (41 : Nat) (@instOfNatNat (41 : Nat))))),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (∀ (_v4 : (@Nat)),
(@Option.{0} (@Bool)))),
(@_v0 (@InputRead.Node.mk _v2 _v3 _v4)))))),
(@_v0 _v1)))) := by
  exact @InputRead.Node.recOn.{u}

-- Independent literal expected type: InputRead.Node.state.
noncomputable def PartACanonical.Types.p0452 :
(∀ (_v0 : (@InputRead.Node)),
(@Fin (@OfNat.ofNat.{0} (@Nat) (41 : Nat) (@instOfNatNat (41 : Nat))))) := by
  exact @InputRead.Node.state

-- Independent literal expected type: InputRead.Node.tape.
noncomputable def PartACanonical.Types.p0453 :
(∀ (_v0 : (@InputRead.Node)),
(∀ (_v1 : (@Nat)),
(@Option.{0} (@Bool)))) := by
  exact @InputRead.Node.tape

-- Independent literal expected type: InputRead.Path.
noncomputable def PartACanonical.Types.p0454 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@InputRead.Node)),
(∀ (_v3 : (@InputRead.Node)),
(Sort 0))))) := by
  exact @InputRead.Path

-- Independent literal expected type: InputRead.Path.append.
noncomputable def PartACanonical.Types.p0455 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@Nat)},
(∀ {_v3 : (@InputRead.Node)},
(∀ {_v4 : (@InputRead.Node)},
(∀ {_v5 : (@InputRead.Node)},
(∀ (_v6 : (@InputRead.Path _v0 _v1 _v3 _v4)),
(∀ (_v7 : (@InputRead.Path _v0 _v2 _v4 _v5)),
(@InputRead.Path _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1 _v2) _v3
  _v5))))))))) := by
  exact @InputRead.Path.append

-- Independent literal expected type: InputRead.Path.below.
noncomputable def PartACanonical.Types.p0456 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (∀ (_v1 : (@Nat)),
(∀ (_v2 : (@InputRead.Node)),
(∀ (_v3 : (@InputRead.Node)),
(∀ (_v4 : (@InputRead.Path _v0 _v1 _v2 _v3)),
(Sort 0)))))},
(∀ {_v2 : (@Nat)},
(∀ {_v3 : (@InputRead.Node)},
(∀ {_v4 : (@InputRead.Node)},
(∀ (_v5 : (@InputRead.Path _v0 _v2 _v3 _v4)),
(Sort 0))))))) := by
  exact @InputRead.Path.below

-- Independent literal expected type: InputRead.Path.below.casesOn.
noncomputable def PartACanonical.Types.p0457 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (∀ (_v1 : (@Nat)),
(∀ (_v2 : (@InputRead.Node)),
(∀ (_v3 : (@InputRead.Node)),
(∀ (_v4 : (@InputRead.Path _v0 _v1 _v2 _v3)),
(Sort 0)))))},
(∀ {_v2 : (∀ {_v2 : (@Nat)},
(∀ {_v3 : (@InputRead.Node)},
(∀ {_v4 : (@InputRead.Node)},
(∀ (_v5 : (@InputRead.Path _v0 _v2 _v3 _v4)),
(∀ (_v6 : (@InputRead.Path.below _v0 _v1 _v2 _v3 _v4 _v5)),
(Sort 0))))))},
(∀ {_v3 : (@Nat)},
(∀ {_v4 : (@InputRead.Node)},
(∀ {_v5 : (@InputRead.Node)},
(∀ {_v6 : (@InputRead.Path _v0 _v3 _v4 _v5)},
(∀ (_v7 : (@InputRead.Path.below _v0 _v1 _v3 _v4 _v5 _v6)),
(∀ (_v8 : (∀ (_v8 : (@InputRead.Node)),
(∀ (_v9 : (@LE.le.{0} (@Nat) (@instLENat) (@InputRead.Node.head _v8) _v0)),
(@_v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v8 _v8 (@InputRead.Path.nil _v0 _v8 _v9)
  (@InputRead.Path.below.nil _v0 _v1 _v8 _v9))))),
(∀ (_v9 : (∀ {_v9 : (@Nat)},
(∀ {_v10 : (@InputRead.Node)},
(∀ {_v11 : (@InputRead.Node)},
(∀ {_v12 : (@InputRead.Node)},
(∀ (_v13 : (@InputRead.Edge _v0 _v10 _v11)),
(∀ {_v14 : (@InputRead.Path _v0 _v9 _v11 _v12)},
(∀ (_v15 : (@InputRead.Path.below _v0 _v1 _v9 _v11 _v12 _v14)),
(∀ (_v16 : (@_v1 _v9 _v11 _v12 _v14)),
(@_v2 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v9 (@OfNat.ofNat.{0} (@Nat) (1 :
  Nat) (@instOfNatNat (1 : Nat)))) _v10 _v12 (@InputRead.Path.cons _v0 _v9 _v10 _v11 _v12 _v13 _v14)
  (@InputRead.Path.below.cons _v0 _v1 _v9 _v10 _v11 _v12 _v13 _v14 _v15 _v16))))))))))),
(@_v2 _v3 _v4 _v5 _v6 _v7))))))))))) := by
  exact @InputRead.Path.below.casesOn

-- Independent literal expected type: InputRead.Path.below.cons.
noncomputable def PartACanonical.Types.p0458 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (∀ (_v1 : (@Nat)),
(∀ (_v2 : (@InputRead.Node)),
(∀ (_v3 : (@InputRead.Node)),
(∀ (_v4 : (@InputRead.Path _v0 _v1 _v2 _v3)),
(Sort 0)))))},
(∀ {_v2 : (@Nat)},
(∀ {_v3 : (@InputRead.Node)},
(∀ {_v4 : (@InputRead.Node)},
(∀ {_v5 : (@InputRead.Node)},
(∀ (_v6 : (@InputRead.Edge _v0 _v3 _v4)),
(∀ {_v7 : (@InputRead.Path _v0 _v2 _v4 _v5)},
(∀ (_v8 : (@InputRead.Path.below _v0 _v1 _v2 _v4 _v5 _v7)),
(∀ (_v9 : (@_v1 _v2 _v4 _v5 _v7)),
(@InputRead.Path.below _v0 _v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v2
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v3 _v5 (@InputRead.Path.cons _v0 _v2 _v3 _v4 _v5 _v6
  _v7)))))))))))) := by
  exact @InputRead.Path.below.cons

-- Independent literal expected type: InputRead.Path.below.nil.
noncomputable def PartACanonical.Types.p0459 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (∀ (_v1 : (@Nat)),
(∀ (_v2 : (@InputRead.Node)),
(∀ (_v3 : (@InputRead.Node)),
(∀ (_v4 : (@InputRead.Path _v0 _v1 _v2 _v3)),
(Sort 0)))))},
(∀ (_v2 : (@InputRead.Node)),
(∀ (_v3 : (@LE.le.{0} (@Nat) (@instLENat) (@InputRead.Node.head _v2) _v0)),
(@InputRead.Path.below _v0 _v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v2 _v2
  (@InputRead.Path.nil _v0 _v2 _v3)))))) := by
  exact @InputRead.Path.below.nil

-- Independent literal expected type: InputRead.Path.below.rec.
noncomputable def PartACanonical.Types.p0460 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (∀ (_v1 : (@Nat)),
(∀ (_v2 : (@InputRead.Node)),
(∀ (_v3 : (@InputRead.Node)),
(∀ (_v4 : (@InputRead.Path _v0 _v1 _v2 _v3)),
(Sort 0)))))},
(∀ {_v2 : (∀ {_v2 : (@Nat)},
(∀ {_v3 : (@InputRead.Node)},
(∀ {_v4 : (@InputRead.Node)},
(∀ (_v5 : (@InputRead.Path _v0 _v2 _v3 _v4)),
(∀ (_v6 : (@InputRead.Path.below _v0 _v1 _v2 _v3 _v4 _v5)),
(Sort 0))))))},
(∀ (_v3 : (∀ (_v3 : (@InputRead.Node)),
(∀ (_v4 : (@LE.le.{0} (@Nat) (@instLENat) (@InputRead.Node.head _v3) _v0)),
(@_v2 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v3 _v3 (@InputRead.Path.nil _v0 _v3 _v4)
  (@InputRead.Path.below.nil _v0 _v1 _v3 _v4))))),
(∀ (_v4 : (∀ {_v4 : (@Nat)},
(∀ {_v5 : (@InputRead.Node)},
(∀ {_v6 : (@InputRead.Node)},
(∀ {_v7 : (@InputRead.Node)},
(∀ (_v8 : (@InputRead.Edge _v0 _v5 _v6)),
(∀ {_v9 : (@InputRead.Path _v0 _v4 _v6 _v7)},
(∀ (_v10 : (@InputRead.Path.below _v0 _v1 _v4 _v6 _v7 _v9)),
(∀ (_v11 : (@_v1 _v4 _v6 _v7 _v9)),
(∀ (_v12 : (@_v2 _v4 _v6 _v7 _v9 _v10)),
(@_v2 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v4 (@OfNat.ofNat.{0} (@Nat) (1 :
  Nat) (@instOfNatNat (1 : Nat)))) _v5 _v7 (@InputRead.Path.cons _v0 _v4 _v5 _v6 _v7 _v8 _v9) (@InputRead.Path.below.cons
  _v0 _v1 _v4 _v5 _v6 _v7 _v8 _v9 _v10 _v11)))))))))))),
(∀ {_v5 : (@Nat)},
(∀ {_v6 : (@InputRead.Node)},
(∀ {_v7 : (@InputRead.Node)},
(∀ {_v8 : (@InputRead.Path _v0 _v5 _v6 _v7)},
(∀ (_v9 : (@InputRead.Path.below _v0 _v1 _v5 _v6 _v7 _v8)),
(@_v2 _v5 _v6 _v7 _v8 _v9))))))))))) := by
  exact @InputRead.Path.below.rec

-- Independent literal expected type: InputRead.Path.bounds.
noncomputable def PartACanonical.Types.p0461 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@InputRead.Node)},
(∀ {_v3 : (@InputRead.Node)},
(∀ (_v4 : (@InputRead.Path _v0 _v1 _v2 _v3)),
(@And (@LE.le.{0} (@Nat) (@instLENat) (@InputRead.Node.head _v2) _v0) (@LE.le.{0} (@Nat) (@instLENat)
  (@InputRead.Node.head _v3) _v0))))))) := by
  exact @InputRead.Path.bounds

-- Independent literal expected type: InputRead.Path.casesOn.
noncomputable def PartACanonical.Types.p0462 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (∀ (_v1 : (@Nat)),
(∀ (_v2 : (@InputRead.Node)),
(∀ (_v3 : (@InputRead.Node)),
(∀ (_v4 : (@InputRead.Path _v0 _v1 _v2 _v3)),
(Sort 0)))))},
(∀ {_v2 : (@Nat)},
(∀ {_v3 : (@InputRead.Node)},
(∀ {_v4 : (@InputRead.Node)},
(∀ (_v5 : (@InputRead.Path _v0 _v2 _v3 _v4)),
(∀ (_v6 : (∀ (_v6 : (@InputRead.Node)),
(∀ (_v7 : (@LE.le.{0} (@Nat) (@instLENat) (@InputRead.Node.head _v6) _v0)),
(@_v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v6 _v6 (@InputRead.Path.nil _v0 _v6 _v7))))),
(∀ (_v7 : (∀ {_v7 : (@Nat)},
(∀ {_v8 : (@InputRead.Node)},
(∀ {_v9 : (@InputRead.Node)},
(∀ {_v10 : (@InputRead.Node)},
(∀ (_v11 : (@InputRead.Edge _v0 _v8 _v9)),
(∀ (_v12 : (@InputRead.Path _v0 _v7 _v9 _v10)),
(@_v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v7 (@OfNat.ofNat.{0} (@Nat) (1 :
  Nat) (@instOfNatNat (1 : Nat)))) _v8 _v10 (@InputRead.Path.cons _v0 _v7 _v8 _v9 _v10 _v11 _v12))))))))),
(@_v1 _v2 _v3 _v4 _v5))))))))) := by
  exact @InputRead.Path.casesOn

-- Independent literal expected type: InputRead.Path.cons.
noncomputable def PartACanonical.Types.p0463 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@InputRead.Node)},
(∀ {_v3 : (@InputRead.Node)},
(∀ {_v4 : (@InputRead.Node)},
(∀ (_v5 : (@InputRead.Edge _v0 _v2 _v3)),
(∀ (_v6 : (@InputRead.Path _v0 _v1 _v3 _v4)),
(@InputRead.Path _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v2 _v4)))))))) := by
  exact @InputRead.Path.cons

-- Independent literal expected type: InputRead.Path.execute.
noncomputable def PartACanonical.Types.p0464 :
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
  _v7))))))))))) := by
  exact @InputRead.Path.execute

-- Independent literal expected type: InputRead.Path.nil.
noncomputable def PartACanonical.Types.p0465 :
(∀ {_v0 : (@Nat)},
(∀ (_v1 : (@InputRead.Node)),
(∀ (_v2 : (@LE.le.{0} (@Nat) (@instLENat) (@InputRead.Node.head _v1) _v0)),
(@InputRead.Path _v0 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v1 _v1)))) := by
  exact @InputRead.Path.nil

-- Independent literal expected type: InputRead.Path.recOn.
noncomputable def PartACanonical.Types.p0467 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (∀ (_v1 : (@Nat)),
(∀ (_v2 : (@InputRead.Node)),
(∀ (_v3 : (@InputRead.Node)),
(∀ (_v4 : (@InputRead.Path _v0 _v1 _v2 _v3)),
(Sort 0)))))},
(∀ {_v2 : (@Nat)},
(∀ {_v3 : (@InputRead.Node)},
(∀ {_v4 : (@InputRead.Node)},
(∀ (_v5 : (@InputRead.Path _v0 _v2 _v3 _v4)),
(∀ (_v6 : (∀ (_v6 : (@InputRead.Node)),
(∀ (_v7 : (@LE.le.{0} (@Nat) (@instLENat) (@InputRead.Node.head _v6) _v0)),
(@_v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v6 _v6 (@InputRead.Path.nil _v0 _v6 _v7))))),
(∀ (_v7 : (∀ {_v7 : (@Nat)},
(∀ {_v8 : (@InputRead.Node)},
(∀ {_v9 : (@InputRead.Node)},
(∀ {_v10 : (@InputRead.Node)},
(∀ (_v11 : (@InputRead.Edge _v0 _v8 _v9)),
(∀ (_v12 : (@InputRead.Path _v0 _v7 _v9 _v10)),
(∀ (_v13 : (@_v1 _v7 _v9 _v10 _v12)),
(@_v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v7 (@OfNat.ofNat.{0} (@Nat) (1 :
  Nat) (@instOfNatNat (1 : Nat)))) _v8 _v10 (@InputRead.Path.cons _v0 _v7 _v8 _v9 _v10 _v11 _v12)))))))))),
(@_v1 _v2 _v3 _v4 _v5))))))))) := by
  exact @InputRead.Path.recOn

-- Independent literal expected type: InputRead.Target.CursorRead.
noncomputable def PartACanonical.Types.p0469 :
(Sort 0) := by
  exact @InputRead.Target.CursorRead

-- Independent literal expected type: InputRead.Target.PartA.
noncomputable def PartACanonical.Types.p0470 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Pnp3.Complexity.Uniform.V1.UniformTM))),
(∀ (_v1 : (∀ (_v1 : (@Nat)),
(@Nat))),
(Sort 0))) := by
  exact @InputRead.Target.PartA

-- Independent literal expected type: InputRead.cursor_exact.
noncomputable def PartACanonical.Types.p0472 :
(@InputRead.Target.CursorRead) := by
  exact @InputRead.cursor_exact

-- Independent literal expected type: InputRead.dest.
noncomputable def PartACanonical.Types.p0473 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Pnp3.Complexity.Uniform.V1.Move)),
(@Nat))) := by
  exact @InputRead.dest

-- Independent literal expected type: InputRead.dest.eq_1.
noncomputable def PartACanonical.Types.p0474 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@InputRead.dest _v0 (@Pnp3.Complexity.Uniform.V1.Move.left)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) := by
  exact @InputRead.dest.eq_1

-- Independent literal complete proposition: InputRead.dest.eq_1.
theorem PartACanonical.Surface.m0274 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@InputRead.dest _v0 (@Pnp3.Complexity.Uniform.V1.Move.left)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) := by
  exact @InputRead.dest.eq_1

-- Independent literal expected type: InputRead.dest.eq_2.
noncomputable def PartACanonical.Types.p0475 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@InputRead.dest _v0 (@Pnp3.Complexity.Uniform.V1.Move.stay)) _v0)) := by
  exact @InputRead.dest.eq_2

-- Independent literal complete proposition: InputRead.dest.eq_2.
theorem PartACanonical.Surface.m0275 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@InputRead.dest _v0 (@Pnp3.Complexity.Uniform.V1.Move.stay)) _v0)) := by
  exact @InputRead.dest.eq_2

-- Independent literal expected type: InputRead.dest.eq_3.
noncomputable def PartACanonical.Types.p0476 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@InputRead.dest _v0 (@Pnp3.Complexity.Uniform.V1.Move.right)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) := by
  exact @InputRead.dest.eq_3

-- Independent literal complete proposition: InputRead.dest.eq_3.
theorem PartACanonical.Surface.m0276 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@InputRead.dest _v0 (@Pnp3.Complexity.Uniform.V1.Move.right)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) := by
  exact @InputRead.dest.eq_3

-- Independent literal expected type: InputRead.embed.
noncomputable def PartACanonical.Types.p0477 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ (_v2 : (@InputRead.Node)),
(∀ (_v3 : (@LT.lt.{0} (@Nat) (@instLTNat) (@InputRead.Node.head _v2) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))),
(@Pnp3.Complexity.Uniform.V1.Config (@OfNat.ofNat.{0} (@Nat) (41 : Nat) (@instOfNatNat (41 : Nat))) _v0 _v1))))) := by
  exact @InputRead.embed

-- Independent literal expected type: InputRead.embed.eq_1.
noncomputable def PartACanonical.Types.p0478 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ (_v2 : (@InputRead.Node)),
(∀ (_v3 : (@LT.lt.{0} (@Nat) (@instLTNat) (@InputRead.Node.head _v2) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@OfNat.ofNat.{0} (@Nat) (41 : Nat) (@instOfNatNat (41 : Nat))) _v0
  _v1) (@InputRead.embed _v0 _v1 _v2 _v3) (@Pnp3.Complexity.Uniform.V1.Config.mk (@OfNat.ofNat.{0} (@Nat) (41 : Nat)
  (@instOfNatNat (41 : Nat))) _v0 _v1 (@InputRead.Node.state _v2) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v0
  _v1) (@InputRead.Node.head _v2) _v3) (fun (_v4 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))) =>
(@InputRead.Node.tape _v2 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v4))))))))) := by
  exact @InputRead.embed.eq_1

-- Independent literal complete proposition: InputRead.embed.eq_1.
theorem PartACanonical.Surface.m0277 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ (_v2 : (@InputRead.Node)),
(∀ (_v3 : (@LT.lt.{0} (@Nat) (@instLTNat) (@InputRead.Node.head _v2) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@OfNat.ofNat.{0} (@Nat) (41 : Nat) (@instOfNatNat (41 : Nat))) _v0
  _v1) (@InputRead.embed _v0 _v1 _v2 _v3) (@Pnp3.Complexity.Uniform.V1.Config.mk (@OfNat.ofNat.{0} (@Nat) (41 : Nat)
  (@instOfNatNat (41 : Nat))) _v0 _v1 (@InputRead.Node.state _v2) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v0
  _v1) (@InputRead.Node.head _v2) _v3) (fun (_v4 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))) =>
(@InputRead.Node.tape _v2 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v4))))))))) := by
  exact @InputRead.embed.eq_1

-- Independent literal expected type: InputRead.hop.
noncomputable def PartACanonical.Types.p0479 :
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
  (@InputRead.Node.mk _v2 _v4 (@InputRead.put _v5 _v3 _v6))))))))))))))) := by
  exact @InputRead.hop

-- Independent literal expected type: InputRead.install_exact.
noncomputable def PartACanonical.Types.p0480 :
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
(@InputRead.install_exact._proof_1 _v0 _v1 _v2 _v3 _v4 _v7 _v8))))) (@Option.none.{0} (@Bool)))),
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
  _v4) _v2 _v3)))))))))))))) := by
  exact @InputRead.install_exact

-- Independent literal expected type: InputRead.install_path.
noncomputable def PartACanonical.Types.p0481 :
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
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v2))))))))) := by
  exact @InputRead.install_path

-- Independent literal expected type: InputRead.keep.
noncomputable def PartACanonical.Types.p0482 :
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
  (@InputRead.Node.mk _v2 _v4 _v5))))))))))))) := by
  exact @InputRead.keep

-- Independent literal expected type: InputRead.machine.
noncomputable def PartACanonical.Types.p0483 :
(@Pnp3.Complexity.Uniform.V1.UniformTM) := by
  exact @InputRead.machine

-- Independent literal expected type: InputRead.modeOf.
noncomputable def PartACanonical.Types.p0484 :
(∀ (_v0 : (@Bool)),
(@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))) := by
  exact @InputRead.modeOf

-- Independent literal expected type: InputRead.modeOf.eq_1.
noncomputable def PartACanonical.Types.p0485 :
(∀ (_v0 : (@Bool)),
(@Eq.{(0 + 1)} (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@InputRead.modeOf _v0) (@ite.{(0 +
  1)} (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Eq.{(0 + 1)} (@Bool) _v0 (@Bool.true))
  (@instDecidableEqBool _v0 (@Bool.true)) (@Fin.mk (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@InputRead.modeOf._proof_1)) (@Fin.mk (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@InputRead.modeOf._proof_2))))) := by
  exact @InputRead.modeOf.eq_1

-- Independent literal complete proposition: InputRead.modeOf.eq_1.
theorem PartACanonical.Surface.m0282 :
(∀ (_v0 : (@Bool)),
(@Eq.{(0 + 1)} (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@InputRead.modeOf _v0) (@ite.{(0 +
  1)} (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Eq.{(0 + 1)} (@Bool) _v0 (@Bool.true))
  (@instDecidableEqBool _v0 (@Bool.true)) (@Fin.mk (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@InputRead.modeOf._proof_1)) (@Fin.mk (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@InputRead.modeOf._proof_2))))) := by
  exact @InputRead.modeOf.eq_1

-- Independent literal expected type: InputRead.put.
noncomputable def PartACanonical.Types.p0486 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Option.{0} (@Bool))),
(∀ (_v3 : (@Nat)),
(@Option.{0} (@Bool)))))) := by
  exact @InputRead.put

-- Independent literal expected type: InputRead.put.eq_1.
noncomputable def PartACanonical.Types.p0487 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Option.{0} (@Bool))),
(∀ (_v3 : (@Nat)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@InputRead.put _v0 _v1 _v2 _v3) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 +
  1)} (@Nat) _v3 _v1) (@instDecidableEqNat _v3 _v1) _v2 (@_v0 _v3))))))) := by
  exact @InputRead.put.eq_1

-- Independent literal complete proposition: InputRead.put.eq_1.
theorem PartACanonical.Surface.m0283 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Option.{0} (@Bool))),
(∀ (_v3 : (@Nat)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@InputRead.put _v0 _v1 _v2 _v3) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 +
  1)} (@Nat) _v3 _v1) (@instDecidableEqNat _v3 _v1) _v2 (@_v0 _v3))))))) := by
  exact @InputRead.put.eq_1

-- Independent literal expected type: InputRead.put_same.
noncomputable def PartACanonical.Types.p0488 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(@Eq.{(0 + 1)} (∀ (_v2 : (@Nat)),
(@Option.{0} (@Bool))) (@InputRead.put _v0 _v1 (@_v0 _v1)) _v0))) := by
  exact @InputRead.put_same

-- Independent literal expected type: InputRead.q.
noncomputable def PartACanonical.Types.p0489 :
(∀ (_v0 : (@Nat)),
(@Fin (@OfNat.ofNat.{0} (@Nat) (41 : Nat) (@instOfNatNat (41 : Nat))))) := by
  exact @InputRead.q

-- Independent literal expected type: InputRead.rawMachine.
noncomputable def PartACanonical.Types.p0490 :
(@Pnp3.Complexity.Uniform.V1.UniformTM) := by
  exact @InputRead.rawMachine

-- Independent literal expected type: InputRead.raw_cursor_parsed.
noncomputable def PartACanonical.Types.p0491 :
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v17))) _v5)) _v16))))))))))))))))))))))))))))))) := by
  exact @InputRead.raw_cursor_parsed

-- Independent literal expected type: InputRead.readClock.
noncomputable def PartACanonical.Types.p0492 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(@Nat)))) := by
  exact @InputRead.readClock

-- Independent literal expected type: InputRead.readClock.eq_1.
noncomputable def PartACanonical.Types.p0493 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@InputRead.readClock _v0 _v1 _v2) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v0) (@HMul.hMul.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v1))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v2)) (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))))))) := by
  exact @InputRead.readClock.eq_1

-- Independent literal complete proposition: InputRead.readClock.eq_1.
theorem PartACanonical.Surface.m0286 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@InputRead.readClock _v0 _v1 _v2) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v0) (@HMul.hMul.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v1))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v2)) (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))))))) := by
  exact @InputRead.readClock.eq_1

-- Independent literal expected type: InputRead.read_path.
noncomputable def PartACanonical.Types.p0494 :
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
  (@Bool)))))))))))))))))))))))) := by
  exact @InputRead.read_path

-- Independent literal expected type: InputRead.ready.
noncomputable def PartACanonical.Types.p0495 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(@Fin (@OfNat.ofNat.{0} (@Nat) (41 : Nat) (@instOfNatNat (41 : Nat))))) := by
  exact @InputRead.ready

-- Independent literal expected type: InputRead.result.
noncomputable def PartACanonical.Types.p0496 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(@Bool)) := by
  exact @InputRead.result

-- Independent literal expected type: InputRead.result.eq_1.
noncomputable def PartACanonical.Types.p0497 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(@Eq.{(0 + 1)} (@Bool) (@InputRead.result _v0) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat)
  (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v0) (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) := by
  exact @InputRead.result.eq_1

-- Independent literal complete proposition: InputRead.result.eq_1.
theorem PartACanonical.Surface.m0288 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(@Eq.{(0 + 1)} (@Bool) (@InputRead.result _v0) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat)
  (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v0) (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))) := by
  exact @InputRead.result.eq_1

-- Independent literal expected type: InputRead.return_path.
noncomputable def PartACanonical.Types.p0498 :
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
  (@instAddNat)) _v1 _v2) _v3) (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) _v0))))))))))) := by
  exact @InputRead.return_path

-- Independent literal expected type: InputRead.return_rows.
noncomputable def PartACanonical.Types.p0499 :
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
  (@Pnp3.Complexity.Uniform.V1.Move) (@Option.none.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Move.stay)))))))))) := by
  exact @InputRead.return_rows

-- Independent literal expected type: InputRead.rows.
noncomputable def PartACanonical.Types.p0500 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (41 : Nat) (@instOfNatNat (41 : Nat))))),
(∀ (_v1 : (@Option.{0} (@Bool))),
(@Prod.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (41 : Nat) (@instOfNatNat (41 : Nat)))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))))) := by
  exact @InputRead.rows

-- Independent literal expected type: InputRead.seed_path.
noncomputable def PartACanonical.Types.p0501 :
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
  _v2)))))))) := by
  exact @InputRead.seed_path

-- Independent literal expected type: InputRead.seek_path.
noncomputable def PartACanonical.Types.p0502 :
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
  (@InputRead.q (@OfNat.ofNat.{0} (@Nat) (7 : Nat) (@instOfNatNat (7 : Nat)))) _v1 _v0))))))))))))))))) := by
  exact @InputRead.seek_path

-- Independent literal expected type: InputRead.stageDeadline.
noncomputable def PartACanonical.Types.p0503 :
(∀ (_v0 : (@Nat)),
(@Nat)) := by
  exact @InputRead.stageDeadline

-- Independent literal expected type: InputRead.stage_clock.
noncomputable def PartACanonical.Types.p0504 :
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
  (@InputRead.stageDeadline _v0)))))))))))) := by
  exact @InputRead.stage_clock

-- Independent literal expected type: InputRead.sweepL.
noncomputable def PartACanonical.Types.p0505 :
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
  (@instAddNat)) _v3 _v4) _v2) (@InputRead.Node.mk _v1 _v3 _v2))))))))) := by
  exact @InputRead.sweepL

-- Independent literal expected type: InputRead.sweepR.
noncomputable def PartACanonical.Types.p0506 :
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
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 _v4) _v2))))))))) := by
  exact @InputRead.sweepR
