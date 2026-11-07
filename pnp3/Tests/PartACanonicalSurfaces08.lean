import Tests.PartACanonicalABI
import Tests.PartAG2InterfaceTests

/-! Infrastructure: mechanical literal restatements of this exact original API.
Proof terms are reused; these are not independently authored correctness proofs.
Type pins, theorem mirrors and direct roots remain separate manifests. -/
set_option autoImplicit false

-- Independent literal expected type for InputRead.Node.noConfusionType.withCtorType.
section
universe u
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0449 :
(∀ (_v0 : (Sort (u + 1))),
(∀ (_v1 : (@Nat)),
(Sort (max ((0 + 1) + 1) (u + 1))))))
end
-- Independent literal expected type for InputRead.Node.rec.
section
universe u
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0450 :
(∀ {_v0 : (∀ (_v0 : (@InputRead.Node)),
(Sort u))},
(∀ (_v1 : (∀ (_v1 : (@Fin (@OfNat.ofNat.{0} (@Nat) (41 : Nat) (@instOfNatNat (41 : Nat))))),
(∀ (_v2 : (@Nat)),
(∀ (_v3 : (∀ (_v3 : (@Nat)),
(@Option.{0} (@Bool)))),
(@_v0 (@InputRead.Node.mk _v1 _v2 _v3)))))),
(∀ (_v2 : (@InputRead.Node)),
(@_v0 _v2)))))
end
-- Independent literal expected type for InputRead.Node.recOn.
section
universe u
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0451 :
(∀ {_v0 : (∀ (_v0 : (@InputRead.Node)),
(Sort u))},
(∀ (_v1 : (@InputRead.Node)),
(∀ (_v2 : (∀ (_v2 : (@Fin (@OfNat.ofNat.{0} (@Nat) (41 : Nat) (@instOfNatNat (41 : Nat))))),
(∀ (_v3 : (@Nat)),
(∀ (_v4 : (∀ (_v4 : (@Nat)),
(@Option.{0} (@Bool)))),
(@_v0 (@InputRead.Node.mk _v2 _v3 _v4)))))),
(@_v0 _v1)))))
end
-- Independent literal expected type for InputRead.Node.state.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0452 :
(∀ (_v0 : (@InputRead.Node)),
(@Fin (@OfNat.ofNat.{0} (@Nat) (41 : Nat) (@instOfNatNat (41 : Nat))))))
end
-- Independent literal expected type for InputRead.Node.tape.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0453 :
(∀ (_v0 : (@InputRead.Node)),
(∀ (_v1 : (@Nat)),
(@Option.{0} (@Bool)))))
end
-- Independent literal expected type for InputRead.Path.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0454 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@InputRead.Node)),
(∀ (_v3 : (@InputRead.Node)),
(Sort 0))))))
end
-- Independent literal expected type for InputRead.Path.append.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0455 :
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
-- Complete literal proposition for InputRead.Path.append; original proof reused.
theorem PartACanonical.Surface.m0269 :
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

-- Independent literal expected type for InputRead.Path.below.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0456 :
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
(Sort 0))))))))
end
-- Independent literal expected type for InputRead.Path.below.casesOn.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0457 :
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
(@_v2 _v3 _v4 _v5 _v6 _v7))))))))))))
end
-- Independent literal expected type for InputRead.Path.below.cons.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0458 :
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
  _v7)))))))))))))
end
-- Independent literal expected type for InputRead.Path.below.nil.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0459 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (∀ (_v1 : (@Nat)),
(∀ (_v2 : (@InputRead.Node)),
(∀ (_v3 : (@InputRead.Node)),
(∀ (_v4 : (@InputRead.Path _v0 _v1 _v2 _v3)),
(Sort 0)))))},
(∀ (_v2 : (@InputRead.Node)),
(∀ (_v3 : (@LE.le.{0} (@Nat) (@instLENat) (@InputRead.Node.head _v2) _v0)),
(@InputRead.Path.below _v0 _v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v2 _v2
  (@InputRead.Path.nil _v0 _v2 _v3)))))))
end
-- Independent literal expected type for InputRead.Path.below.rec.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0460 :
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
(@_v2 _v5 _v6 _v7 _v8 _v9))))))))))))
end
-- Independent literal expected type for InputRead.Path.bounds.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0461 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@InputRead.Node)},
(∀ {_v3 : (@InputRead.Node)},
(∀ (_v4 : (@InputRead.Path _v0 _v1 _v2 _v3)),
(@And (@LE.le.{0} (@Nat) (@instLENat) (@InputRead.Node.head _v2) _v0) (@LE.le.{0} (@Nat) (@instLENat)
  (@InputRead.Node.head _v3) _v0))))))))
end
-- Complete literal proposition for InputRead.Path.bounds; original proof reused.
theorem PartACanonical.Surface.m0270 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@InputRead.Node)},
(∀ {_v3 : (@InputRead.Node)},
(∀ (_v4 : (@InputRead.Path _v0 _v1 _v2 _v3)),
(@And (@LE.le.{0} (@Nat) (@instLENat) (@InputRead.Node.head _v2) _v0) (@LE.le.{0} (@Nat) (@instLENat)
  (@InputRead.Node.head _v3) _v0))))))) := by
  exact @InputRead.Path.bounds

-- Independent literal expected type for InputRead.Path.casesOn.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0462 :
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
(@_v1 _v2 _v3 _v4 _v5))))))))))
end
-- Independent literal expected type for InputRead.Path.cons.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0463 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ {_v2 : (@InputRead.Node)},
(∀ {_v3 : (@InputRead.Node)},
(∀ {_v4 : (@InputRead.Node)},
(∀ (_v5 : (@InputRead.Edge _v0 _v2 _v3)),
(∀ (_v6 : (@InputRead.Path _v0 _v1 _v3 _v4)),
(@InputRead.Path _v0 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v1
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) _v2 _v4)))))))))
end
-- Independent literal expected type for InputRead.Path.execute.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0464 :
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
-- Complete literal proposition for InputRead.Path.execute; original proof reused.
theorem PartACanonical.Surface.m0271 :
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

-- Independent literal expected type for InputRead.Path.nil.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0465 :
(∀ {_v0 : (@Nat)},
(∀ (_v1 : (@InputRead.Node)),
(∀ (_v2 : (@LE.le.{0} (@Nat) (@instLENat) (@InputRead.Node.head _v1) _v0)),
(@InputRead.Path _v0 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v1 _v1)))))
end
-- Independent literal expected type for InputRead.Path.rec.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0466 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (∀ (_v1 : (@Nat)),
(∀ (_v2 : (@InputRead.Node)),
(∀ (_v3 : (@InputRead.Node)),
(∀ (_v4 : (@InputRead.Path _v0 _v1 _v2 _v3)),
(Sort 0)))))},
(∀ (_v2 : (∀ (_v2 : (@InputRead.Node)),
(∀ (_v3 : (@LE.le.{0} (@Nat) (@instLENat) (@InputRead.Node.head _v2) _v0)),
(@_v1 (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat))) _v2 _v2 (@InputRead.Path.nil _v0 _v2 _v3))))),
(∀ (_v3 : (∀ {_v3 : (@Nat)},
(∀ {_v4 : (@InputRead.Node)},
(∀ {_v5 : (@InputRead.Node)},
(∀ {_v6 : (@InputRead.Node)},
(∀ (_v7 : (@InputRead.Edge _v0 _v4 _v5)),
(∀ (_v8 : (@InputRead.Path _v0 _v3 _v5 _v6)),
(∀ (_v9 : (@_v1 _v3 _v5 _v6 _v8)),
(@_v1 (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v3 (@OfNat.ofNat.{0} (@Nat) (1 :
  Nat) (@instOfNatNat (1 : Nat)))) _v4 _v6 (@InputRead.Path.cons _v0 _v3 _v4 _v5 _v6 _v7 _v8)))))))))),
(∀ {_v4 : (@Nat)},
(∀ {_v5 : (@InputRead.Node)},
(∀ {_v6 : (@InputRead.Node)},
(∀ (_v7 : (@InputRead.Path _v0 _v4 _v5 _v6)),
(@_v1 _v4 _v5 _v6 _v7))))))))))
end
-- Independent literal expected type for InputRead.Path.recOn.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0467 :
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
(@_v1 _v2 _v3 _v4 _v5))))))))))
end
-- Independent literal expected type for InputRead.Prototype.dump.
noncomputable def PartACanonical.Types.p0468 :
(∀ (_v0 : (@String)),
(∀ (_v1 : (@Pnp3.Complexity.Uniform.V1.UniformTM)),
(@IO (@Unit)))) := by
  exact @InputRead.Prototype.dump

-- Independent literal expected type for InputRead.Target.CursorRead.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0469 :
(Sort 0))
end
-- Independent literal expected type for InputRead.Target.PartA.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0470 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Pnp3.Complexity.Uniform.V1.UniformTM))),
(∀ (_v1 : (∀ (_v1 : (@Nat)),
(@Nat))),
(Sort 0))))
end
-- Independent literal expected type for InputRead.accepted_cursor.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0471 :
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
-- Complete literal proposition for InputRead.accepted_cursor; original proof reused.
theorem PartACanonical.Surface.m0272 :
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
  (@Pnp4.Frontier.ContractExpansion.thresholdPoly _v0)) _v14))) _v6)) _v13))))))))))))))))))))))))))))))) := by
  exact @InputRead.accepted_cursor

-- Independent literal expected type for InputRead.cursor_exact.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0472 :
(@InputRead.Target.CursorRead))
end
-- Complete literal proposition for InputRead.cursor_exact; original proof reused.
theorem PartACanonical.Surface.m0273 :
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
  (@instSubNat)) _v2 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@InputRead.Target.CursorRead._proof_6
  _v0 _v1 _v2 _v3 _v4 _v5 _v7 _v8 _v9))) (@Option.none.{0} (@Bool)))),
(∀ (_v13 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@InputRead.machine)) _v0 _v1 _v6 (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHSub.{0} (@Nat)
  (@instSubNat)) _v2 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@InputRead.Target.CursorRead._proof_7
  _v0 _v1 _v2 _v3 _v4 _v5 _v7 _v8 _v9))) (@Option.some.{0} (@Bool) (@Bool.true)))),
(∀ (_v14 : (∀ (_v14 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))),
(∀ (_v15 : (@LE.le.{0} (@Nat) (@instLENat) _v2 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v14))),
(∀ (_v16 : (@LT.lt.{0} (@Nat) (@instLTNat) (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v14) _v3)),
(@Exists.{(0 + 1)} (@Bool) (fun (_v17 : (@Bool)) =>
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@InputRead.machine)) _v0 _v1 _v6 _v14) (@Option.some.{0} (@Bool)
  _v17)))))))),
(∀ (_v15 : (@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@Pnp3.Complexity.Uniform.V1.Config.tape
  (@Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (@InputRead.machine)) _v0 _v1 _v6 (@Fin.mk
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v3 (@InputRead.Target.CursorRead._proof_8 _v0 _v1 _v2 _v3 _v4 _v5
  _v9))) (@Option.none.{0} (@Bool)))),
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
  (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@InputRead.Target.CursorRead._proof_9 _v0 _v1 _v2 _v3
  _v4 _v5 _v9))) (@Option.none.{0} (@Bool)))),
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
  (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v2 (@InputRead.Target.CursorRead._proof_10 _v0 _v1 _v2 _v3 _v4 _v5 _v8
  _v9))) (@Option.some.{0} (@Bool) (@InputRead.result _v20)))) (let _v21 : (@Pnp3.Complexity.Uniform.V1.Config
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
  _v6 _v22))))))))))))))))))))))))))))))) := by
  exact @InputRead.cursor_exact

-- Independent literal expected type for InputRead.dest.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0473 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Pnp3.Complexity.Uniform.V1.Move)),
(@Nat))))
end
-- Independent literal expected type for InputRead.dest.eq_1.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0474 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@InputRead.dest _v0 (@Pnp3.Complexity.Uniform.V1.Move.left)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))))
end
-- Complete literal proposition for InputRead.dest.eq_1; original proof reused.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Surface.m0274 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@InputRead.dest _v0 (@Pnp3.Complexity.Uniform.V1.Move.left)) (@HSub.hSub.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHSub.{0} (@Nat) (@instSubNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))))
end
-- Independent literal expected type for InputRead.dest.eq_2.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0475 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@InputRead.dest _v0 (@Pnp3.Complexity.Uniform.V1.Move.stay)) _v0)))
end
-- Complete literal proposition for InputRead.dest.eq_2; original proof reused.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Surface.m0275 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@InputRead.dest _v0 (@Pnp3.Complexity.Uniform.V1.Move.stay)) _v0)))
end
-- Independent literal expected type for InputRead.dest.eq_3.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0476 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@InputRead.dest _v0 (@Pnp3.Complexity.Uniform.V1.Move.right)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))))
end
-- Complete literal proposition for InputRead.dest.eq_3; original proof reused.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Surface.m0276 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@InputRead.dest _v0 (@Pnp3.Complexity.Uniform.V1.Move.right)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat)
  (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) _v0 (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))))
end
-- Independent literal expected type for InputRead.embed.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0477 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ (_v2 : (@InputRead.Node)),
(∀ (_v3 : (@LT.lt.{0} (@Nat) (@instLTNat) (@InputRead.Node.head _v2) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))),
(@Pnp3.Complexity.Uniform.V1.Config (@OfNat.ofNat.{0} (@Nat) (41 : Nat) (@instOfNatNat (41 : Nat))) _v0 _v1))))))
end
-- Independent literal expected type for InputRead.embed.eq_1.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0478 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ (_v2 : (@InputRead.Node)),
(∀ (_v3 : (@LT.lt.{0} (@Nat) (@instLTNat) (@InputRead.Node.head _v2) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@OfNat.ofNat.{0} (@Nat) (41 : Nat) (@instOfNatNat (41 : Nat))) _v0
  _v1) (@InputRead.embed _v0 _v1 _v2 _v3) (@Pnp3.Complexity.Uniform.V1.Config.mk (@OfNat.ofNat.{0} (@Nat) (41 : Nat)
  (@instOfNatNat (41 : Nat))) _v0 _v1 (@InputRead.Node.state _v2) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v0
  _v1) (@InputRead.Node.head _v2) _v3) (fun (_v4 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))) =>
(@InputRead.Node.tape _v2 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v4))))))))))
end
-- Complete literal proposition for InputRead.embed.eq_1; original proof reused.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Surface.m0277 :
(∀ {_v0 : (@Nat)},
(∀ {_v1 : (@Nat)},
(∀ (_v2 : (@InputRead.Node)),
(∀ (_v3 : (@LT.lt.{0} (@Nat) (@instLTNat) (@InputRead.Node.head _v2) (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))),
(@Eq.{(0 + 1)} (@Pnp3.Complexity.Uniform.V1.Config (@OfNat.ofNat.{0} (@Nat) (41 : Nat) (@instOfNatNat (41 : Nat))) _v0
  _v1) (@InputRead.embed _v0 _v1 _v2 _v3) (@Pnp3.Complexity.Uniform.V1.Config.mk (@OfNat.ofNat.{0} (@Nat) (41 : Nat)
  (@instOfNatNat (41 : Nat))) _v0 _v1 (@InputRead.Node.state _v2) (@Fin.mk (@Pnp3.Complexity.Uniform.V1.tapeLength _v0
  _v1) (@InputRead.Node.head _v2) _v3) (fun (_v4 : (@Fin (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1))) =>
(@InputRead.Node.tape _v2 (@Fin.val (@Pnp3.Complexity.Uniform.V1.tapeLength _v0 _v1) _v4))))))))))
end
-- Independent literal expected type for InputRead.hop.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0479 :
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
-- Complete literal proposition for InputRead.hop; original proof reused.
theorem PartACanonical.Surface.m0278 :
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

-- Independent literal expected type for InputRead.install_exact.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0480 :
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
  _v4) _v2 _v3)))))))))))))))
end
-- Complete literal proposition for InputRead.install_exact; original proof reused.
theorem PartACanonical.Surface.m0279 :
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

-- Independent literal expected type for InputRead.install_path.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0481 :
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
-- Complete literal proposition for InputRead.install_path; original proof reused.
theorem PartACanonical.Surface.m0280 :
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

-- Independent literal expected type for InputRead.keep.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0482 :
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
-- Complete literal proposition for InputRead.keep; original proof reused.
theorem PartACanonical.Surface.m0281 :
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

-- Independent literal expected type for InputRead.machine.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0483 :
(@Pnp3.Complexity.Uniform.V1.UniformTM))
end
-- Independent literal expected type for InputRead.modeOf.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0484 :
(∀ (_v0 : (@Bool)),
(@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))))
end
-- Independent literal expected type for InputRead.modeOf.eq_1.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0485 :
(∀ (_v0 : (@Bool)),
(@Eq.{(0 + 1)} (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@InputRead.modeOf _v0) (@ite.{(0 +
  1)} (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Eq.{(0 + 1)} (@Bool) _v0 (@Bool.true))
  (@instDecidableEqBool _v0 (@Bool.true)) (@Fin.mk (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@InputRead.modeOf._proof_1)) (@Fin.mk (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@InputRead.modeOf._proof_2))))))
end
-- Complete literal proposition for InputRead.modeOf.eq_1; original proof reused.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Surface.m0282 :
(∀ (_v0 : (@Bool)),
(@Eq.{(0 + 1)} (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@InputRead.modeOf _v0) (@ite.{(0 +
  1)} (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))) (@Eq.{(0 + 1)} (@Bool) _v0 (@Bool.true))
  (@instDecidableEqBool _v0 (@Bool.true)) (@Fin.mk (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat)))
  (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat))) (@InputRead.modeOf._proof_1)) (@Fin.mk (@OfNat.ofNat.{0}
  (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat) (@instOfNatNat (0 : Nat)))
  (@InputRead.modeOf._proof_2))))))
end
-- Independent literal expected type for InputRead.put.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0486 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Option.{0} (@Bool))),
(∀ (_v3 : (@Nat)),
(@Option.{0} (@Bool)))))))
end
-- Independent literal expected type for InputRead.put.eq_1.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0487 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Option.{0} (@Bool))),
(∀ (_v3 : (@Nat)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@InputRead.put _v0 _v1 _v2 _v3) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 +
  1)} (@Nat) _v3 _v1) (@instDecidableEqNat _v3 _v1) _v2 (@_v0 _v3))))))))
end
-- Complete literal proposition for InputRead.put.eq_1; original proof reused.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Surface.m0283 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Option.{0} (@Bool))),
(∀ (_v3 : (@Nat)),
(@Eq.{(0 + 1)} (@Option.{0} (@Bool)) (@InputRead.put _v0 _v1 _v2 _v3) (@ite.{(0 + 1)} (@Option.{0} (@Bool)) (@Eq.{(0 +
  1)} (@Nat) _v3 _v1) (@instDecidableEqNat _v3 _v1) _v2 (@_v0 _v3))))))))
end
-- Independent literal expected type for InputRead.put_same.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0488 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(@Eq.{(0 + 1)} (∀ (_v2 : (@Nat)),
(@Option.{0} (@Bool))) (@InputRead.put _v0 _v1 (@_v0 _v1)) _v0))))
end
-- Complete literal proposition for InputRead.put_same; original proof reused.
theorem PartACanonical.Surface.m0284 :
(∀ (_v0 : (∀ (_v0 : (@Nat)),
(@Option.{0} (@Bool)))),
(∀ (_v1 : (@Nat)),
(@Eq.{(0 + 1)} (∀ (_v2 : (@Nat)),
(@Option.{0} (@Bool))) (@InputRead.put _v0 _v1 (@_v0 _v1)) _v0))) := by
  exact @InputRead.put_same

-- Independent literal expected type for InputRead.q.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0489 :
(∀ (_v0 : (@Nat)),
(@Fin (@OfNat.ofNat.{0} (@Nat) (41 : Nat) (@instOfNatNat (41 : Nat))))))
end
-- Independent literal expected type for InputRead.rawMachine.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0490 :
(@Pnp3.Complexity.Uniform.V1.UniformTM))
end
-- Independent literal expected type for InputRead.raw_cursor_parsed.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0491 :
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
-- Complete literal proposition for InputRead.raw_cursor_parsed; original proof reused.
theorem PartACanonical.Surface.m0285 :
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

-- Independent literal expected type for InputRead.readClock.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0492 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(@Nat)))))
end
-- Independent literal expected type for InputRead.readClock.eq_1.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0493 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@InputRead.readClock _v0 _v1 _v2) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v0) (@HMul.hMul.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v1))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v2)) (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))))))))
end
-- Complete literal proposition for InputRead.readClock.eq_1; original proof reused.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Surface.m0286 :
(∀ (_v0 : (@Nat)),
(∀ (_v1 : (@Nat)),
(∀ (_v2 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@InputRead.readClock _v0 _v1 _v2) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0}
  (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HAdd.hAdd.{0, 0,
  0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0}
  (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v0) (@HMul.hMul.{0, 0, 0} (@Nat)
  (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat))) _v1))
  (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} (@Nat) (@instMulNat)) (@OfNat.ofNat.{0} (@Nat) (2 : Nat)
  (@instOfNatNat (2 : Nat))) _v2)) (@OfNat.ofNat.{0} (@Nat) (11 : Nat) (@instOfNatNat (11 : Nat)))))))))
end
-- Independent literal expected type for InputRead.read_path.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0494 :
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
-- Complete literal proposition for InputRead.read_path; original proof reused.
theorem PartACanonical.Surface.m0287 :
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

-- Independent literal expected type for InputRead.ready.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0495 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(@Fin (@OfNat.ofNat.{0} (@Nat) (41 : Nat) (@instOfNatNat (41 : Nat))))))
end
-- Independent literal expected type for InputRead.result.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0496 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(@Bool)))
end
-- Independent literal expected type for InputRead.result.eq_1.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0497 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(@Eq.{(0 + 1)} (@Bool) (@InputRead.result _v0) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat)
  (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v0) (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))))
end
-- Complete literal proposition for InputRead.result.eq_1; original proof reused.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Surface.m0288 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))))),
(@Eq.{(0 + 1)} (@Bool) (@InputRead.result _v0) (@BEq.beq.{0} (@Nat) (@instBEqOfDecidableEq.{0} (@Nat)
  (@instDecidableEqNat)) (@Fin.val (@OfNat.ofNat.{0} (@Nat) (3 : Nat) (@instOfNatNat (3 : Nat))) _v0) (@OfNat.ofNat.{0}
  (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))))))
end
-- Independent literal expected type for InputRead.return_path.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0498 :
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
-- Complete literal proposition for InputRead.return_path; original proof reused.
theorem PartACanonical.Surface.m0289 :
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

-- Independent literal expected type for InputRead.return_rows.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0499 :
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
-- Complete literal proposition for InputRead.return_rows; original proof reused.
theorem PartACanonical.Surface.m0290 :
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

-- Independent literal expected type for InputRead.rows.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0500 :
(∀ (_v0 : (@Fin (@OfNat.ofNat.{0} (@Nat) (41 : Nat) (@instOfNatNat (41 : Nat))))),
(∀ (_v1 : (@Option.{0} (@Bool))),
(@Prod.{0, 0} (@Fin (@OfNat.ofNat.{0} (@Nat) (41 : Nat) (@instOfNatNat (41 : Nat)))) (@Prod.{0, 0} (@Option.{0} (@Bool))
  (@Pnp3.Complexity.Uniform.V1.Move))))))
end
-- Independent literal expected type for InputRead.seed_path.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0501 :
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
-- Complete literal proposition for InputRead.seed_path; original proof reused.
theorem PartACanonical.Surface.m0291 :
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

-- Independent literal expected type for InputRead.seek_path.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0502 :
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
-- Complete literal proposition for InputRead.seek_path; original proof reused.
theorem PartACanonical.Surface.m0292 :
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

-- Independent literal expected type for InputRead.stageDeadline.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0503 :
(∀ (_v0 : (@Nat)),
(@Nat)))
end
-- Independent literal expected type for InputRead.stage_clock.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0504 :
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
-- Complete literal proposition for InputRead.stage_clock; original proof reused.
theorem PartACanonical.Surface.m0293 :
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

-- Independent literal expected type for InputRead.sweepL.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0505 :
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
-- Complete literal proposition for InputRead.sweepL; original proof reused.
theorem PartACanonical.Surface.m0294 :
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

-- Independent literal expected type for InputRead.sweepR.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.p0506 :
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
-- Complete literal proposition for InputRead.sweepR; original proof reused.
theorem PartACanonical.Surface.m0295 :
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

-- Independent literal expected type for Nat.log2.eq_1.
noncomputable def PartACanonical.Types.p0507 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@Nat.log2 _v0) (@ite.{(0 + 1)} (@Nat) (@GE.ge.{0} (@Nat) (@instLENat) _v0 (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@Nat.decLe (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v0) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Nat.log2 (@HDiv.hDiv.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHDiv.{0} (@Nat) (@Nat.instDiv)) _v0 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))))) := by
  exact @Nat.log2.eq_1

-- Complete literal proposition for Nat.log2.eq_1; original proof reused.
theorem PartACanonical.Surface.m0296 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@Nat.log2 _v0) (@ite.{(0 + 1)} (@Nat) (@GE.ge.{0} (@Nat) (@instLENat) _v0 (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@Nat.decLe (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v0) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Nat.log2 (@HDiv.hDiv.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHDiv.{0} (@Nat) (@Nat.instDiv)) _v0 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))))) := by
  exact @Nat.log2.eq_1

-- Independent literal expected type for Nat.log2.eq_def.
noncomputable def PartACanonical.Types.p0508 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@Nat.log2 _v0) (@ite.{(0 + 1)} (@Nat) (@GE.ge.{0} (@Nat) (@instLENat) _v0 (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@Nat.decLe (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v0) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Nat.log2 (@HDiv.hDiv.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHDiv.{0} (@Nat) (@Nat.instDiv)) _v0 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))))) := by
  exact @Nat.log2.eq_def

-- Complete literal proposition for Nat.log2.eq_def; original proof reused.
theorem PartACanonical.Surface.m0297 :
(∀ (_v0 : (@Nat)),
(@Eq.{(0 + 1)} (@Nat) (@Nat.log2 _v0) (@ite.{(0 + 1)} (@Nat) (@GE.ge.{0} (@Nat) (@instLENat) _v0 (@OfNat.ofNat.{0}
  (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))) (@Nat.decLe (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 : Nat)))
  _v0) (@HAdd.hAdd.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHAdd.{0} (@Nat) (@instAddNat)) (@Nat.log2 (@HDiv.hDiv.{0, 0, 0}
  (@Nat) (@Nat) (@Nat) (@instHDiv.{0} (@Nat) (@Nat.instDiv)) _v0 (@OfNat.ofNat.{0} (@Nat) (2 : Nat) (@instOfNatNat (2 :
  Nat))))) (@OfNat.ofNat.{0} (@Nat) (1 : Nat) (@instOfNatNat (1 : Nat)))) (@OfNat.ofNat.{0} (@Nat) (0 : Nat)
  (@instOfNatNat (0 : Nat)))))) := by
  exact @Nat.log2.eq_def
