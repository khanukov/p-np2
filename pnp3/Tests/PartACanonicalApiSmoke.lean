import Tests.PartAInputReadSurfaceTests
import Tests.PartABodySurfaceTests

/-! C0 elaborator API smoke for the unchanged first7 and G1 sources.
The environment inventory is evidence for surface planning. It does not generate
independent proofs or substitute inferred types for explicit proposition mirrors. -/
open Lean Elab Command

namespace Pnp3.Tests.PartACanonicalApiSmoke

private def forallArity : Expr → Nat
  | .forallE _ _ body _ => 1 + forallArity body
  | _ => 0

-- Exercise the exact-owner private-name API before designing large consumers.
run_cmd do
  let env ← getEnv
  let owner := `Complexity.Uniform.V1.FixedRawLengthFenceCountdown
  let name := Name.str (Name.append (Name.num (Name.append `_private owner) 0)
    `Pnp3.Complexity.Uniform.V1.FixedRawLengthFence) "geometry"
  let some (.thmInfo _) := env.find? name | throwError "Missing private smoke target {name}"
  let some idx := env.getModuleIdxFor? name | throwError "Missing private smoke owner"
  unless env.header.moduleNames[idx]! == owner do throwError "Wrong private smoke owner"
  logInfo m!"C0_PRIVATE_OWNER|{owner}|{name}"
  modifyScope fun s => {s with openDecls := .explicit (Name.str .anonymous "countdown_geometry") name :: s.openDecls}

open Pnp3.Complexity.Uniform.V1 PairEncoding

theorem check_countdown_geometry {a m B z : Nat} (x : Bitstring a) (w : Bitstring m)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some z)
    (hr : 2 * pairLength a m + 2 ≤ B) :
    9 + z ≤ a + m ∧
      a + m + 3 + z + FixedRawLengthFence.capacity a m z =
        FixedRawLengthFence.fencePos (pairLength a m) ∧
      FixedRawLengthFence.fencePos (pairLength a m) < tapeLength (pairLength a m) B := by
  exact countdown_geometry x w hg hr

run_cmd do
  let env ← getEnv
  let owners := #[`Body.Machine, `Body.Path, `Body.Target, `Body.Proof, `Body.Raw,
    `AcceptedBody.Target, `AcceptedBody.Closure, `InputRead.Machine, `InputRead.Path,
    `InputRead.Target, `InputRead.Proof, `InputRead.Raw]
  let mut count := 0
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let owner := env.header.moduleNames[idx]!
      if owners.contains owner then
        let isProposition ← liftTermElabM <| Meta.isProp info.type
        let propositionValued ← liftTermElabM <| Meta.forallTelescopeReducing info.type fun _ result =>
          pure result.isProp
        let privateTypeReferences := info.type.getUsedConstants.filter isPrivateName
        let kind := match info with
          | .thmInfo _ => "theorem"
          | .defnInfo _ => "definition"
          | .ctorInfo _ => "constructor"
          | .recInfo _ => "recursor"
          | .inductInfo _ => "inductive"
          | .opaqueInfo _ => "opaque"
          | .axiomInfo _ => "axiom-info"
          | .quotInfo _ => "quotient"
        let record := Json.mkObj [
          ("owner", toJson owner.toString), ("name", toJson name.toString),
          ("userName", toJson (privateToUserName name).toString),
          ("private", toJson (isPrivateName name)), ("kind", toJson kind),
          ("proposition", toJson isProposition), ("propositionValued", toJson propositionValued),
          ("privateTypeReferences", toJson (privateTypeReferences.map Name.toString)),
          ("forallArity", toJson (forallArity info.type)),
          ("typeExpr", toJson ((repr info.type).pretty 1000000000))]
        logInfo m!"C0_DECL|{record.compress}"
        count := count + 1
  unless count > 100 do throwError "C0 environment inventory unexpectedly small: {count}"
  logInfo m!"C0_DECL_COUNT|{count}"

-- Direct roots are explicit commands, separate from the type and mirror inventories.
#print axioms InputRead.cursor_exact
#print axioms InputRead.accepted_cursor
#print axioms Pnp3.Tests.PartAInputReadSurfaceTests.check_InputRead_cursor_exact
#print axioms Pnp3.Tests.PartAInputReadSurfaceTests.check_InputRead_accepted_cursor
#print axioms Body.round_exact
#print axioms AcceptedBody.exact
#print axioms countdown_geometry
#print axioms check_countdown_geometry

end Pnp3.Tests.PartACanonicalApiSmoke
