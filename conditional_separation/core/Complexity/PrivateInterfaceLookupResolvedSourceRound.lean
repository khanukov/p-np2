import Complexity.PrivateInterfaceLookupResolvedControl
open Lean Elab Command
namespace PartAPrivateSourceRound
/- Finite source-backed metadata contracts, not independently expected full types. -/
private def contracts : Name → Option (List (Name × Name × String × List Name × String))
  | `FullIngressClosure.SourceArena => some [
    (`BodyIngress.Native, `BodyIngress.Node.mk, "constructor", [], "pNode"),
    (`BodyIngress.Native, `BodyIngress.Path, "inductive", [], "PPath"),
    (`BodyIngress.Native, `BodyIngress.Path.append, "theorem", [], "pAppend"),
    (`BodyIngress.Native, `BodyIngress.keep, "theorem", [], "pKeep"),
    (`BodyIngress.Native, `BodyIngress.sweepL, "theorem", [], "pSweepL"),
    (`BodyIngress.Native, `BodyIngress.sweepR, "theorem", [], "pSweepR"),
    (`BodyIngress.Native, `BodyIngress.dest, "definition", [], "dest"),
    (`SerializedBodyRefinement.Proof, `SerializedBodyRefinement.Grid, "inductive", [], "Grid"),
    (`SerializedBodyRefinement.Proof, `SerializedBodyRefinement.Grid.mono, "theorem", [], "gridMono"),
    (`SerializedBodyRefinement.Proof, `SerializedBodyRefinement.Grid.blank, "theorem", [], "gridBlank"),
    (`FullIngressClosure.Paths, `FullIngressClosure.Safe, "definition", [], "Safe"),
    (`FullIngressClosure.Move, `FullIngressClosure.Travel, "inductive", [], "Travel"),
    (`FullIngressClosure.Move, `FullIngressClosure.travel, "theorem", [], "travel"),
    (`FullIngressClosure.Workspace, `FullIngressClosure.setBank, "definition", [], "setBank")]
  | `FullIngressClosure.SourceCertificates => some [
    (`FullIngressClosure.SourceArena, `FullIngressClosure.ToHCode, "inductive", [], "ToHCode"),
    (`FullIngressClosure.SourceArena, `FullIngressClosure.ToHCode.mk, "constructor", [], "toHMk"),
    (`FullIngressClosure.SourceArena, `FullIngressClosure.FromHCode, "inductive", [], "FromHCode"),
    (`FullIngressClosure.SourceArena, `FullIngressClosure.FromHCode.mk, "constructor", [], "fromHMk"),
    (`FullIngressClosure.SourceScan, `FullIngressClosure.ToHoleCode, "inductive", [], "ToHoleCode"),
    (`FullIngressClosure.SourceScan, `FullIngressClosure.ToHoleCode.mk, "constructor", [], "holeMk"),
    (`FullIngressClosure.SourceScan, `FullIngressClosure.RegReturnCode, "inductive", [], "RegReturnCode"),
    (`FullIngressClosure.SourceScan, `FullIngressClosure.RegReturnCode.mk, "constructor", [], "regReturnMk"),
    (`FullIngressClosure.SourceScan, `FullIngressClosure.SourceReturnCode, "inductive", [], "SourceReturnCode"),
    (`FullIngressClosure.SourceScan, `FullIngressClosure.SourceReturnCode.mk, "constructor", [], "sourceReturnMk"),
    (`FullIngressClosure.Move, `FullIngressClosure.Travel.right, "constructor", [], "trRight"),
    (`FullIngressClosure.Move, `FullIngressClosure.Travel.left, "constructor", [], "trLeft"),
    (`FullIngressClosure.Move, `FullIngressClosure.Travel.stay, "constructor", [], "trStay"),
    (`FullIngressClosure.Paths, `FullIngressClosure.RouteR.nil, "constructor", [], "rrNil"),
    (`FullIngressClosure.Paths, `FullIngressClosure.RouteR.next, "constructor", [], "rrNext"),
    (`FullIngressClosure.Paths, `FullIngressClosure.RouteL.nil, "constructor", [], "rlNil"),
    (`FullIngressClosure.Paths, `FullIngressClosure.RouteL.next, "constructor", [], "rlNext"),
    (`FullIngressClosure.Rows, `FullIngressClosure.native_row, "theorem", [], "nativeRow"),
    (`FullIngressClosure.Certificates, `FullIngressClosure.st, "definition", [], "st"),
    (`FullIngressClosure.Certificates, `FullIngressClosure.st_small, "theorem", [], "stSmall"),
    (`FullIngressClosure.Certificates, `FullIngressClosure.safeNative, "theorem", [], "safeNative")]
  | `FullIngressClosure.SourceBackRound => some [
    (`BodyIngress.Native, `BodyIngress.Node.mk, "constructor", [], "pNode"),
    (`BodyIngress.Native, `BodyIngress.Path, "inductive", [], "PPath"),
    (`BodyIngress.Native, `BodyIngress.Path.append, "theorem", [], "pAppend"),
    (`BodyIngress.Native, `BodyIngress.put, "definition", [], "put"),
    (`BodyIngress.Native, `BodyIngress.dest, "definition", [], "dest"),
    (`SerializedBodyRefinement.Proof, `SerializedBodyRefinement.Grid, "inductive", [], "Grid"),
    (`SerializedBodyRefinement.Proof, `SerializedBodyRefinement.Grid.mono, "theorem", [], "gridMono"),
    (`SerializedBodyRefinement.Proof, `SerializedBodyRefinement.Grid.blank, "theorem", [], "gridBlank"),
    (`SerializedBodyRefinement.Proof, `SerializedBodyRefinement.Unary, "definition", [], "BankUnary"),
    (`FullIngressClosure.Paths, `FullIngressClosure.Safe, "definition", [], "Safe"),
    (`FullIngressClosure.Paths, `FullIngressClosure.hop, "theorem", [], "hop"),
    (`FullIngressClosure.Workspace, `FullIngressClosure.setBank, "definition", [], "setBank"),
    (`FullIngressClosure.Workspace, `FullIngressClosure.bank_grid, "theorem", [], "bankGrid"),
    (`FullIngressClosure.Workspace, `FullIngressClosure.bank_unary, "theorem", [], "bankUnary"),
    (`FullIngressClosure.Workspace, `FullIngressClosure.bank_take, "theorem", [], "bankTake"),
    (`FullIngressClosure.Move, `FullIngressClosure.asUnary, "theorem", [], "asUnary"),
    (`FullIngressClosure.Counters, `FullIngressClosure.Decrement, "inductive", [], "Decrement"),
    (`FullIngressClosure.Counters, `FullIngressClosure.decrement_positive, "theorem", [], "decrementPositive"),
    (`FullIngressClosure.SourceArena, `FullIngressClosure.Arena, "inductive", [], "Arena"),
    (`FullIngressClosure.SourceArena, `FullIngressClosure.Arena.gap, "theorem", [], "arenaGap"),
    (`FullIngressClosure.SourceScan, `FullIngressClosure.Corridor, "inductive", [], "Corridor"),
    (`FullIngressClosure.SourceScan, `FullIngressClosure.Corridor.order, "theorem", [], "corridorOrder"),
    (`FullIngressClosure.SourceScan, `FullIngressClosure.Corridor.eof, "theorem", [], "corridorEof"),
    (`FullIngressClosure.SourceScan, `FullIngressClosure.ToHoleCode, "inductive", [], "ToHoleCode"),
    (`FullIngressClosure.SourceScan, `FullIngressClosure.to_source_hole, "theorem", [], "toSource"),
    (`FullIngressClosure.SourceScan, `FullIngressClosure.SourceReturnCode, "inductive", [], "SourceReturnCode"),
    (`FullIngressClosure.SourceScan, `FullIngressClosure.from_source_hole, "theorem", [], "fromSource"),
    (`FullIngressClosure.SourceImage, `FullIngressClosure.lifted, "definition", [], "lifted"),
    (`FullIngressClosure.SourceImage, `FullIngressClosure.lifted_here, "theorem", [], "liftedHere"),
    (`FullIngressClosure.SourceImage, `FullIngressClosure.restore_lifted, "theorem", [], "restoreLifted"),
    (`FullIngressClosure.SourceImage, `FullIngressClosure.bank_lifted, "theorem", [], "bankLifted"),
    (`FullIngressClosure.SourceImage, `FullIngressClosure.lifted_grid, "theorem", [], "liftedGrid"),
    (`FullIngressClosure.SourceImage, `FullIngressClosure.lifted_unary, "theorem", [], "liftedUnary"),
    (`FullIngressClosure.SourceImage, `FullIngressClosure.bank_below, "theorem", [], "bankBelow"),
    (`FullIngressClosure.SourceImage, `FullIngressClosure.bank_corridor, "theorem", [], "bankCorridor"),
    (`FullIngressClosure.SourceImage, `FullIngressClosure.bank_arena, "theorem", [], "bankArena"),
    (`FullIngressClosure.SourceImage, `FullIngressClosure.lifted_corridor, "theorem", [], "liftedCorridor"),
    (`FullIngressClosure.SourceImage, `FullIngressClosure.lifted_arena, "theorem", [], "liftedArena"),
    (`FullIngressClosure.SourceImage, `FullIngressClosure.lifted_old, "theorem", [], "liftedOld"),
    (`FullIngressClosure.SourceImage, `FullIngressClosure.put_here, "theorem", [], "putHere")]
  | `FullIngressClosure.SourceRoundCertificates => some [
    (`FullIngressClosure.SourceBackRound, `FullIngressClosure.BackCode, "inductive", [], "BackCode"),
    (`FullIngressClosure.SourceBackRound, `FullIngressClosure.BackCode.mk, "constructor", [], "backMk"),
    (`FullIngressClosure.SourceCertificates, `FullIngressClosure.hole1393, "definition", [], "hole1393"),
    (`FullIngressClosure.SourceCertificates, `FullIngressClosure.hole1429, "definition", [], "hole1429"),
    (`FullIngressClosure.SourceCertificates, `FullIngressClosure.hole1465, "definition", [], "hole1465"),
    (`FullIngressClosure.SourceCertificates, `FullIngressClosure.sourceReturn1495, "definition", [], "sourceReturn1495"),
    (`FullIngressClosure.SourceCertificates, `FullIngressClosure.sourceReturn1521, "definition", [], "sourceReturn1521"),
    (`FullIngressClosure.Certificates, `FullIngressClosure.dec1389, "definition", [], "dec1389"),
    (`FullIngressClosure.Certificates, `FullIngressClosure.dec1425, "definition", [], "dec1425"),
    (`FullIngressClosure.Certificates, `FullIngressClosure.dec1461, "definition", [], "dec1461"),
    (`FullIngressClosure.Certificates, `FullIngressClosure.st, "definition", [], "st"),
    (`FullIngressClosure.Certificates, `FullIngressClosure.st_small, "theorem", [], "stSmall"),
    (`FullIngressClosure.Certificates, `FullIngressClosure.safeNative, "theorem", [], "safeNative"),
    (`FullIngressClosure.Rows, `FullIngressClosure.native_row, "theorem", [], "nativeRow"),
    (`FullIngressClosure.Move, `FullIngressClosure.Travel, "inductive", [], "Travel"),
    (`FullIngressClosure.Move, `FullIngressClosure.Travel.left, "constructor", [], "trLeft"),
    (`FullIngressClosure.Paths, `FullIngressClosure.RouteL.nil, "constructor", [], "rlNil"),
    (`FullIngressClosure.Paths, `FullIngressClosure.RouteL.next, "constructor", [], "rlNext")]
  | _ => none
def batch (env : Environment) (rows : List (Name × Name × String × List Name × String)) : Except String (List (Name × String)) :=
  rows.mapM fun (owner,user,kind,universes,aliasName) => do
    return (← PartAPrivateControl.resolve env owner user owner kind universes, aliasName)
def bindings (group : Name) : CommandElabM (List (Name × String)) := do
  let some rows := contracts group | throwError "source-round/domain"
  ofExcept (batch (← getEnv) rows)
#check (batch : Environment → List (Name × Name × String × List Name × String) → Except String (List (Name × String)))
#check (bindings : Name → CommandElabM (List (Name × String)))
#check (contracts : Name → Option (List (Name × Name × String × List Name × String)))
#print axioms batch
#print axioms bindings
#print axioms contracts
end PartAPrivateSourceRound
