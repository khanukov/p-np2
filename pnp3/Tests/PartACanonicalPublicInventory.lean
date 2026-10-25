import Tests.PartACanonicalRootTests

/-! Infrastructure: actual public environment inventory, without private auxiliary
expression trees. This does not substitute for explicit proposition mirrors,
typed consumers or direct central axiom roots. -/
open Lean Elab Command
namespace FullFinalClosure.CanonicalC1Inventory

private def arity : Expr → Nat
  | .forallE _ _ body _ => 1 + arity body
  | _ => 0
private def returnsProp : Expr → Bool
  | .forallE _ _ body _ => returnsProp body
  | result => result.isProp
private def exposed (n : Name) : Bool :=
  !isPrivateName n && !n.isInternal && !(n.toString.splitOn ".").any
    (fun part => "_".isPrefixOf part || "match_".isPrefixOf part)

run_cmd do
  let env ← getEnv
  let families : List String := ["AcceptedBody", "AllArityBitLength", "AllArityCounted", "AllArityCursor", "AllArityWorkspace", "BitLengthDriver", "Body", "BodyIngress", "CanonicalLeaf", "CappedWeight", "CappedWorkspace", "CarryReadyCompletion", "CarryWindow", "CertificateGuardClosure", "ConnectedRead", "Cursor", "FullBodyClosure", "FullFinalClosure", "FullIngressClosure", "FullWeight", "GammaSupport", "IngressAllocation", "IngressRepair", "InputRead", "NormalClockClosure", "NormalFinalClosure", "PhysicalCallerClosure", "PostWeight", "PowerDriver", "RawCallerClosure", "RawFrontier", "RawPrelude", "RepairedFrontier", "RuntimeBitLength", "SerializedBody", "SerializedBodyCompletion", "SerializedBodyRefinement", "SerializedPositiveBody", "SmallIngress", "SmallOrbit", "StandardTMBridgeClosure", "Stream", "SuffixCap", "TotalIngressClosure", "UniformClassBridgeClosure", "VirtualFinalClosure", "VirtualLeaf", "VirtualReady", "VirtualReadyPins"]
  let mut count := 0
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let owner := env.header.moduleNames[idx]!
      if families.contains (owner.toString.splitOn ".").head! && exposed name then
        let kind := match info with
          | .thmInfo _ => "theorem"
          | .defnInfo _ => "definition"
          | .ctorInfo _ => "constructor"
          | .recInfo _ => "recursor"
          | .inductInfo _ => "inductive"
          | .opaqueInfo _ => "opaque"
          | .axiomInfo _ => "axiom-info"
          | .quotInfo _ => "quotient"
        let privateRefs := info.type.getUsedConstants.filter isPrivateName
        let record := Json.mkObj [("name", toJson name.toString),
          ("owner", toJson owner.toString), ("kind", toJson kind),
          ("forallArity", toJson (arity info.type)),
          ("syntacticPropositionValued", toJson (returnsProp info.type)),
          ("levelParams", toJson (info.levelParams.map Name.toString)),
          ("typeHash64", toJson (toString (hash info.type))),
          ("privateTypeReferences", toJson (privateRefs.map Name.toString))]
        logInfo m!"C1_PUBLIC|{record.compress}"
        count := count + 1
  unless count > 100 do throwError "Unexpectedly small C1 public environment: {count}"
  let some idx := env.getModuleIdxFor? `FullFinalClosure.full_endpoint_full
    | throwError "Missing actual public endpoint owner"
  unless env.header.moduleNames[idx]! == `FullFinalClosure.Surface do
    throwError "Wrong actual public endpoint owner"
  logInfo m!"C1_PUBLIC_COUNT|{count}"

end FullFinalClosure.CanonicalC1Inventory
