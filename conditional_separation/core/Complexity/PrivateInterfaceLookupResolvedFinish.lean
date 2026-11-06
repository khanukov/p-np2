import Complexity.PrivateInterfaceLookupResolvedControl
open Lean Elab Command
namespace PartAPrivateFinish
/- Finite source-backed metadata contracts, not independently expected full types. -/
private def contracts : Name → Option (List (Name × Name × String × List Name × String))
  | `FullIngressClosure.PhysicalFrame => some [
    (`SerializedBodyRefinement.Proof, `SerializedBodyRefinement.Unary, "definition", [], "BankUnary"),
    (`FullIngressClosure.Initialization, `FullIngressClosure.Six, "inductive", [], "Six"),
    (`FullIngressClosure.Initialization, `FullIngressClosure.Six.mk, "constructor", [], "sixMk"),
    (`FullIngressClosure.ArithmeticStage, `FullIngressClosure.initialValues, "definition", [], "initialValues"),
    (`FullIngressClosure.SourceArena, `FullIngressClosure.Arena, "inductive", [], "Arena"),
    (`FullIngressClosure.SourceArena, `FullIngressClosure.Arena.mk, "constructor", [], "arenaMk"),
    (`FullIngressClosure.SourceScan, `FullIngressClosure.Corridor, "inductive", [], "Corridor"),
    (`FullIngressClosure.SourceScan, `FullIngressClosure.Corridor.mk, "constructor", [], "corridorMk")]
  | `FullIngressClosure.CounterExterior => some [
    (`FullIngressClosure.CounterFront, `FullIngressClosure.counterTape, "definition", [], "counterTape"),
    (`FullIngressClosure.ArithmeticStage, `FullIngressClosure.arithmeticTape, "definition", [], "arithmeticTape"),
    (`FullIngressClosure.HalfDriver, `FullIngressClosure.halfPhase, "definition", [], "halfPhase"),
    (`FullIngressClosure.Move, `FullIngressClosure.image3, "definition", [], "image3"),
    (`FullIngressClosure.Workspace, `FullIngressClosure.setBank, "definition", [], "setBank"),
    (`FullIngressClosure.Initialization, `FullIngressClosure.stageTape, "definition", [], "stageTape"),
    (`FullIngressClosure.Initialization, `FullIngressClosure.partial_old, "theorem", [], "partialOld"),
    (`FullIngressClosure.Initialization, `FullIngressClosure.Before, "definition", [], "Before"),
    (`FullIngressClosure.Initialization, `FullIngressClosure.before_below, "theorem", [], "beforeBelow"),
    (`FullIngressClosure.Initialization, `FullIngressClosure.delimiter_mono, "theorem", [], "delimiterMono"),
    (`FullIngressClosure.SourceArena, `FullIngressClosure.Arena, "inductive", [], "Arena"),
    (`FullIngressClosure.SourceArena, `FullIngressClosure.Arena.mk, "constructor", [], "arenaMk"),
    (`FullIngressClosure.SourceArena, `FullIngressClosure.Arena.positive, "theorem", [], "arenaPositive"),
    (`FullIngressClosure.SourceArena, `FullIngressClosure.Arena.gap, "theorem", [], "arenaGap"),
    (`FullIngressClosure.SourceArena, `FullIngressClosure.Arena.blank, "theorem", [], "arenaBlank"),
    (`FullIngressClosure.SourceArena, `FullIngressClosure.Arena.fence, "theorem", [], "arenaFence"),
    (`FullIngressClosure.SourceArena, `FullIngressClosure.Arena.marks, "theorem", [], "arenaMarks"),
    (`FullIngressClosure.SourceArena, `FullIngressClosure.Arena.space, "theorem", [], "arenaSpace"),
    (`FullIngressClosure.SourceScan, `FullIngressClosure.Corridor, "inductive", [], "Corridor"),
    (`FullIngressClosure.SourceScan, `FullIngressClosure.Corridor.mk, "constructor", [], "corridorMk"),
    (`FullIngressClosure.SourceScan, `FullIngressClosure.Corridor.order, "theorem", [], "corridorOrder"),
    (`FullIngressClosure.SourceScan, `FullIngressClosure.Corridor.eof, "theorem", [], "corridorEof"),
    (`FullIngressClosure.SourceScan, `FullIngressClosure.Corridor.sep, "theorem", [], "corridorSep"),
    (`FullIngressClosure.SourceScan, `FullIngressClosure.Corridor.endBlank, "theorem", [], "corridorBlank"),
    (`FullIngressClosure.SourceScan, `FullIngressClosure.Corridor.register, "theorem", [], "corridorRegister"),
    (`FullIngressClosure.SourceScan, `FullIngressClosure.Corridor.assignment, "theorem", [], "corridorAssignment")]
  | `FullIngressClosure.FinalImage => some [
    (`BodyIngress.Native, `BodyIngress.put, "definition", [], "put"),
    (`SerializedBodyRefinement.Proof, `SerializedBodyRefinement.Grid, "inductive", [], "Grid"),
    (`SerializedBodyRefinement.Proof, `SerializedBodyRefinement.Grid.blank, "theorem", [], "gridBlank"),
    (`SerializedBodyRefinement.Proof, `SerializedBodyRefinement.Unary, "definition", [], "BankUnary"),
    (`FullIngressClosure.SourceImage, `FullIngressClosure.lifted, "definition", [], "lifted")]
  | `FullIngressClosure.FinishStage => some [
    (`BodyIngress.Native, `BodyIngress.Node.mk, "constructor", [], "pNode"),
    (`BodyIngress.Native, `BodyIngress.Path, "inductive", [], "PPath"),
    (`BodyIngress.Native, `BodyIngress.Path.append, "theorem", [], "pAppend"),
    (`BodyIngress.Native, `BodyIngress.keep, "theorem", [], "pKeep"),
    (`SerializedBodyRefinement.Proof, `SerializedBodyRefinement.Grid, "inductive", [], "Grid"),
    (`SerializedBodyRefinement.Proof, `SerializedBodyRefinement.Grid.mono, "theorem", [], "gridMono"),
    (`SerializedBodyRefinement.Proof, `SerializedBodyRefinement.Grid.blank, "theorem", [], "gridBlank"),
    (`SerializedBodyRefinement.Proof, `SerializedBodyRefinement.Grid.cells, "theorem", [], "gridCells"),
    (`FullIngressClosure.Paths, `FullIngressClosure.Safe, "definition", [], "Safe"),
    (`FullIngressClosure.Workspace, `FullIngressClosure.setBank, "definition", [], "setBank"),
    (`FullIngressClosure.Workspace, `FullIngressClosure.bank_grid, "theorem", [], "bankGrid"),
    (`FullIngressClosure.Move, `FullIngressClosure.Travel, "inductive", [], "Travel"),
    (`FullIngressClosure.Move, `FullIngressClosure.travel, "theorem", [], "travel"),
    (`FullIngressClosure.Paint, `FullIngressClosure.PaintCode, "inductive", [], "PaintCode"),
    (`FullIngressClosure.Paint, `FullIngressClosure.paint, "theorem", [], "paint"),
    (`FullIngressClosure.HalvingStage, `FullIngressClosure.painted_bank, "theorem", [], "paintedBank"),
    (`FullIngressClosure.SourceArena, `FullIngressClosure.Arena, "inductive", [], "Arena"),
    (`FullIngressClosure.SourceArena, `FullIngressClosure.Arena.blank, "theorem", [], "arenaBlank"),
    (`FullIngressClosure.SourceArena, `FullIngressClosure.Arena.gap, "theorem", [], "arenaGap"),
    (`FullIngressClosure.SourceArena, `FullIngressClosure.ToHCode, "inductive", [], "ToHCode"),
    (`FullIngressClosure.SourceArena, `FullIngressClosure.to_assignment_end, "theorem", [], "toH"),
    (`FullIngressClosure.SourceImage, `FullIngressClosure.bank_arena, "theorem", [], "bankArena")]
  | `FullIngressClosure.FinishCertificates => some [
    (`FullIngressClosure.FinishStage, `FullIngressClosure.FinishStageCode, "inductive", [], "FinishStageCode"),
    (`FullIngressClosure.FinishStage, `FullIngressClosure.FinishStageCode.mk, "constructor", [], "finishStageMk"),
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
    (`FullIngressClosure.Certificates, `FullIngressClosure.safeNative, "theorem", [], "safeNative"),
    (`FullIngressClosure.PaintCertificates, `FullIngressClosure.paint1879, "definition", [], "paint1879"),
    (`FullIngressClosure.PaintCertificates, `FullIngressClosure.paint1886, "definition", [], "paint1886"),
    (`FullIngressClosure.PaintCertificates, `FullIngressClosure.paint1891, "definition", [], "paint1891"),
    (`FullIngressClosure.PaintCertificates, `FullIngressClosure.paint1937, "definition", [], "paint1937"),
    (`FullIngressClosure.PaintCertificates, `FullIngressClosure.paint1944, "definition", [], "paint1944"),
    (`FullIngressClosure.PaintCertificates, `FullIngressClosure.paint1949, "definition", [], "paint1949"),
    (`FullIngressClosure.PaintCertificates, `FullIngressClosure.paint1995, "definition", [], "paint1995"),
    (`FullIngressClosure.PaintCertificates, `FullIngressClosure.paint2002, "definition", [], "paint2002"),
    (`FullIngressClosure.PaintCertificates, `FullIngressClosure.paint2007, "definition", [], "paint2007"),
    (`FullIngressClosure.SourceCertificates, `FullIngressClosure.toH1894, "definition", [], "toH1894"),
    (`FullIngressClosure.SourceCertificates, `FullIngressClosure.toH1952, "definition", [], "toH1952"),
    (`FullIngressClosure.SourceCertificates, `FullIngressClosure.toH2010, "definition", [], "toH2010")]
  | `FullIngressClosure.FinishPrepared => some [
    (`BodyIngress.Native, `BodyIngress.Node.mk, "constructor", [], "pNode"),
    (`BodyIngress.Native, `BodyIngress.Path, "inductive", [], "PPath"),
    (`SerializedBodyRefinement.Proof, `SerializedBodyRefinement.Grid, "inductive", [], "Grid"),
    (`SerializedBodyRefinement.Proof, `SerializedBodyRefinement.Grid.mono, "theorem", [], "gridMono"),
    (`FullIngressClosure.Registers, `FullIngressClosure.Registers, "inductive", [], "Registers"),
    (`FullIngressClosure.Registers, `FullIngressClosure.Registers.mk, "constructor", [], "registersMk"),
    (`FullIngressClosure.Registers, `FullIngressClosure.Registers.grid, "theorem", [], "registerGrid"),
    (`FullIngressClosure.Registers, `FullIngressClosure.Registers.unary, "theorem", [], "registerUnary"),
    (`FullIngressClosure.Registers, `FullIngressClosure.registers_set, "theorem", [], "registersSet"),
    (`FullIngressClosure.Workspace, `FullIngressClosure.setBank, "definition", [], "setBank"),
    (`FullIngressClosure.Workspace, `FullIngressClosure.bank_grid, "theorem", [], "bankGrid"),
    (`FullIngressClosure.SourceArena, `FullIngressClosure.Arena, "inductive", [], "Arena"),
    (`FullIngressClosure.SourceArena, `FullIngressClosure.Arena.gap, "theorem", [], "arenaGap"),
    (`FullIngressClosure.SourceScan, `FullIngressClosure.Corridor, "inductive", [], "Corridor"),
    (`FullIngressClosure.SourceScan, `FullIngressClosure.Corridor.order, "theorem", [], "corridorOrder"),
    (`FullIngressClosure.SourceImage, `FullIngressClosure.lifted, "definition", [], "lifted"),
    (`FullIngressClosure.SourceImage, `FullIngressClosure.bank_lifted, "theorem", [], "bankLifted"),
    (`FullIngressClosure.SourceImage, `FullIngressClosure.lifted_grid, "theorem", [], "liftedGrid"),
    (`FullIngressClosure.SourceImage, `FullIngressClosure.lifted_arena, "theorem", [], "liftedArena"),
    (`FullIngressClosure.FinishStage, `FullIngressClosure.finish_stage, "theorem", [], "finishStage"),
    (`FullIngressClosure.FinishCertificates, `FullIngressClosure.finishState, "definition", [], "finishState"),
    (`FullIngressClosure.FinishCertificates, `FullIngressClosure.finishCases, "definition", [], "finishCases"),
    (`FullIngressClosure.FinalImage, `FullIngressClosure.endpointValues, "definition", [], "endpointValues"),
    (`FullIngressClosure.FinalImage, `FullIngressClosure.complete_image, "theorem", [], "completeImage"),
    (`FullIngressClosure.FinalImage, `FullIngressClosure.lifted_prepared, "theorem", [], "liftedPrepared")]
  | `FullIngressClosure.EndRegisters => some [
    (`FullIngressClosure.Registers, `FullIngressClosure.Registers, "inductive", [], "Registers"),
    (`FullIngressClosure.Registers, `FullIngressClosure.Registers.mk, "constructor", [], "registersMk"),
    (`FullIngressClosure.Registers, `FullIngressClosure.Registers.grid, "theorem", [], "registerGrid"),
    (`FullIngressClosure.Registers, `FullIngressClosure.Registers.unary, "theorem", [], "registerUnary"),
    (`FullIngressClosure.Registers, `FullIngressClosure.registers_set, "theorem", [], "registersSet"),
    (`FullIngressClosure.CounterFront, `FullIngressClosure.counterValues, "definition", [], "counterValues"),
    (`FullIngressClosure.Workspace, `FullIngressClosure.setBank, "definition", [], "setBank"),
    (`FullIngressClosure.Workspace, `FullIngressClosure.bank_original, "theorem", [], "bankOriginal"),
    (`FullIngressClosure.SourceSkipDriver, `FullIngressClosure.skipTape, "definition", [], "skipTape"),
    (`FullIngressClosure.FinishPrepared, `FullIngressClosure.endValues, "definition", [], "endValues"),
    (`SerializedBodyRefinement.Proof, `SerializedBodyRefinement.Unary, "definition", [], "BankUnary")]
  | `FullIngressClosure.Environment => some [
    (`SerializedBodyRefinement.Proof, `SerializedBodyRefinement.Grid, "inductive", [], "Grid"),
    (`FullIngressClosure.Workspace, `FullIngressClosure.setBank, "definition", [], "setBank"),
    (`FullIngressClosure.SourceArena, `FullIngressClosure.Arena, "inductive", [], "Arena"),
    (`FullIngressClosure.SourceArena, `FullIngressClosure.Arena.gap, "theorem", [], "arenaGap"),
    (`FullIngressClosure.SourceScan, `FullIngressClosure.Corridor, "inductive", [], "Corridor"),
    (`FullIngressClosure.SourceScan, `FullIngressClosure.Corridor.order, "theorem", [], "corridorOrder"),
    (`FullIngressClosure.SourceImage, `FullIngressClosure.bank_corridor, "theorem", [], "bankCorridor"),
    (`FullIngressClosure.SourceImage, `FullIngressClosure.bank_arena, "theorem", [], "bankArena"),
    (`FullIngressClosure.SourceImage, `FullIngressClosure.bank_below, "theorem", [], "bankBelow"),
    (`FullIngressClosure.FinishPrepared, `FullIngressClosure.bank_exterior, "theorem", [], "bankExterior")]
  | _ => none
def batch (env : Environment) (rows : List (Name × Name × String × List Name × String)) : Except String (List (Name × String)) :=
  rows.mapM fun (owner,user,kind,universes,aliasName) => do
    return (← PartAPrivateControl.resolve env owner user owner kind universes, aliasName)
def bindings (group : Name) : CommandElabM (List (Name × String)) := do
  let some rows := contracts group | throwError "finish-frame/domain"
  ofExcept (batch (← getEnv) rows)
#check (batch : Environment → List (Name × Name × String × List Name × String) → Except String (List (Name × String)))
#check (bindings : Name → CommandElabM (List (Name × String)))
#check (contracts : Name → Option (List (Name × Name × String × List Name × String)))
#print axioms batch
#print axioms bindings
#print axioms contracts
end PartAPrivateFinish
