import Tests.PartACanonicalAuditSupport
import Tests.PartACanonicalABI
import Tests.PartAG2InterfaceTests

/-! Infrastructure: mechanical literal restatements of this exact original API.
Proof terms are reused; these are not independently authored correctness proofs.
Type pins, theorem mirrors and direct roots remain separate manifests. -/
set_option autoImplicit false

-- Independent literal expected type for PartACanonical.Audit.directAxioms.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.e0001 :
(@Lean.ParserDescr))
end
-- Independent literal expected type for PartACanonical.Audit.elaborateDirectAxioms.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.e0002 :
(@Lean.Elab.Command.CommandElab))
end
-- Independent literal expected type for PartACanonical.Audit.printDirect.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.e0003 :
(∀ (_v0 : (@String)),
(@Lean.Elab.Command.CommandElabM (@Unit))))
end
-- Independent literal expected type for PartACanonical.Audit.printDirect.match_1.
section
universe u_1
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.e0004 :
(∀ (_v0 : (∀ (_v0 : (@Option.{0} (@Lean.Name))),
(Sort u_1))),
(∀ (_v1 : (@Option.{0} (@Lean.Name))),
(∀ (_v2 : (∀ (_v2 : (@Lean.Name)),
(@_v0 (@Option.some.{0} (@Lean.Name) _v2)))),
(∀ (_v3 : (∀ (_v3 : (@Option.{0} (@Lean.Name))),
(@_v0 _v3))),
(@_v0 _v1))))))
end
-- Independent literal expected type for PartACanonical.Audit.printDirect.match_3.
section
universe u_1
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.e0005 :
(∀ (_v0 : (∀ (_v0 : (@Prod.{0, 0} (@Lean.Name) (@Lean.ConstantInfo))),
(Sort u_1))),
(∀ (_v1 : (@Prod.{0, 0} (@Lean.Name) (@Lean.ConstantInfo))),
(∀ (_v2 : (∀ (_v2 : (@Lean.Name)),
(∀ (_v3 : (@Lean.ConstantInfo)),
(@_v0 (@Prod.mk.{0, 0} (@Lean.Name) (@Lean.ConstantInfo) _v2 _v3))))),
(@_v0 _v1)))))
end
-- Independent literal expected type for PartACanonical.Audit.printDirect.match_5.
section
universe u_1
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.e0006 :
(∀ (_v0 : (∀ (_v0 : (@Option.{0} (@Std.HashMap.{0, 0} (@String) (@Lean.Name) (@instBEqOfDecidableEq.{0} (@String)
  (@instDecidableEqString)) (@instHashableString)))),
(Sort u_1))),
(∀ (_v1 : (@Option.{0} (@Std.HashMap.{0, 0} (@String) (@Lean.Name) (@instBEqOfDecidableEq.{0} (@String)
  (@instDecidableEqString)) (@instHashableString)))),
(∀ (_v2 : (∀ (_v2 : (@Std.HashMap.{0, 0} (@String) (@Lean.Name) (@instBEqOfDecidableEq.{0} (@String)
  (@instDecidableEqString)) (@instHashableString))),
(@_v0 (@Option.some.{0} (@Std.HashMap.{0, 0} (@String) (@Lean.Name) (@instBEqOfDecidableEq.{0} (@String)
  (@instDecidableEqString)) (@instHashableString)) _v2)))),
(∀ (_v3 : (∀ (_v3 : (@Unit)),
(@_v0 (@Option.none.{0} (@Std.HashMap.{0, 0} (@String) (@Lean.Name) (@instBEqOfDecidableEq.{0} (@String)
  (@instDecidableEqString)) (@instHashableString)))))),
(@_v0 _v1))))))
end
-- Independent literal expected type for PartACanonical.elaboratePrivateABI.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.e0007 :
(@Lean.Elab.Term.TermElab))
end
-- Independent literal expected type for PartACanonical.elaboratePrivateABI.match_1.
section
universe u_1
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.e0008 :
(∀ (_v0 : (∀ (_v0 : (@Option.{0} (@Lean.ModuleIdx))),
(Sort u_1))),
(∀ (_v1 : (@Option.{0} (@Lean.ModuleIdx))),
(∀ (_v2 : (∀ (_v2 : (@Lean.ModuleIdx)),
(@_v0 (@Option.some.{0} (@Lean.ModuleIdx) _v2)))),
(∀ (_v3 : (∀ (_v3 : (@Option.{0} (@Lean.ModuleIdx))),
(@_v0 _v3))),
(@_v0 _v1))))))
end
-- Independent literal expected type for PartACanonical.privateABI.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.e0009 :
(@Lean.ParserDescr))
end
-- Independent literal expected type for PartACanonical.privateNameFromString.
section
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.e0010 :
(∀ (_v0 : (@String)),
(@Lean.Name)))
end
-- Independent literal expected type for PartACanonical.privateNameFromString.match_1.
section
universe u_1
-- Existing named accepted literal; independent complete C2 expected-type ascription.
#check (@PartACanonical.Types.e0011 :
(∀ (_v0 : (∀ (_v0 : (@Option.{0} (@Nat))),
(Sort u_1))),
(∀ (_v1 : (@Option.{0} (@Nat))),
(∀ (_v2 : (∀ (_v2 : (@Nat)),
(@_v0 (@Option.some.{0} (@Nat) _v2)))),
(∀ (_v3 : (∀ (_v3 : (@Unit)),
(@_v0 (@Option.none.{0} (@Nat))))),
(@_v0 _v1))))))
end
