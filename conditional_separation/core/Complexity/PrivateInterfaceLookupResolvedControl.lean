import Lean
/- Exact metadata identity on the current environment. Not independent full-signature
   validation. The finite textual adapter supports the frozen published literal domain;
   arbitrary strings, empty components and unsupported ConstantInfo kinds are rejected. -/
open Lean Elab Tactic Command
namespace PartAPrivateControl
def resolve (env : Environment) (encodedOwner user actualOwner : Name)
    (kind : String) (universes : List Name) : Except String Name := do
  let n := mkPrivateNameCore encodedOwner user
  let some ci := env.find? n | throw "control/missing"
  unless ci.name == n do throw "control/name"
  let good := match ci with
    | .defnInfo _ => kind == "definition"
    | .thmInfo _ => kind == "theorem"
    | .inductInfo _ => kind == "inductive"
    | .ctorInfo _ => kind == "constructor"
    | _ => false
  unless good do throw "control/kind"
  let some idx := env.getModuleIdxFor? n | throw "control/owner"
  let some owner := env.header.moduleNames[idx.toNat]? | throw "control/owner-index"
  unless owner == actualOwner do throw "control/owner"
  unless ci.levelParams == universes do throw "control/universes"
  return n
private def contracts : List (Name × Name × String) := [
  (`AllArityBitLength.Raw, `AllArityBitLength.Cells, "inductive"),
  (`AllArityBitLength.Raw, `AllArityBitLength.Cells.arena, "theorem"),
  (`AllArityBitLength.Raw, `AllArityBitLength.Cells.assn, "theorem"),
  (`AllArityBitLength.Raw, `AllArityBitLength.Cells.eof, "theorem"),
  (`AllArityBitLength.Raw, `AllArityBitLength.Cells.fence, "theorem"),
  (`AllArityBitLength.Raw, `AllArityBitLength.Cells.gap, "theorem"),
  (`AllArityBitLength.Raw, `AllArityBitLength.Cells.marks, "theorem"),
  (`AllArityBitLength.Raw, `AllArityBitLength.Cells.reg, "theorem"),
  (`AllArityBitLength.Raw, `AllArityBitLength.Cells.right, "theorem"),
  (`AllArityBitLength.Raw, `AllArityBitLength.Cells.sep, "theorem"),
  (`AllArityBitLength.Raw, `AllArityBitLength.Cells.source, "theorem"),
  (`AllArityBitLength.Raw, `AllArityBitLength.actual_cells, "theorem"),
  (`AllArityBitLength.Raw, `AllArityBitLength.body, "theorem"),
  (`AllArityBitLength.Raw, `AllArityBitLength.clock, "theorem"),
  (`AllArityBitLength.Raw, `AllArityBitLength.overflow_address, "theorem"),
  (`AllArityWorkspace.Runtime, `AllArityWorkspace.suffix_bound, "theorem"),
  (`BitLengthDriver.Kernel, `BitLengthDriver.Frame.mk, "constructor"),
  (`BitLengthDriver.Kernel, `BitLengthDriver.Path.execute, "theorem"),
  (`BitLengthDriver.Kernel, `BitLengthDriver.Path.first, "theorem"),
  (`BitLengthDriver.Kernel, `BitLengthDriver.initial_image, "theorem"),
  (`BitLengthDriver.Kernel, `BitLengthDriver.length_step, "theorem"),
  (`BitLengthDriver.Kernel, `BitLengthDriver.loop, "theorem"),
  (`BitLengthDriver.Kernel, `BitLengthDriver.outcome, "definition"),
  (`BitLengthDriver.Kernel, `BitLengthDriver.row_value, "theorem"),
  (`CanonicalLeaf.Rows, `CanonicalLeaf.region_step, "theorem"),
  (`CanonicalLeaf.Rows, `CanonicalLeaf.transport, "theorem"),
  (`CappedWeight.Kernel, `CappedWeight.Frame, "inductive"),
  (`CappedWeight.Kernel, `CappedWeight.Frame.mk, "constructor"),
  (`CappedWeight.Kernel, `CappedWeight.assignment, "theorem"),
  (`CappedWeight.Kernel, `CappedWeight.atD, "theorem"),
  (`CappedWeight.Kernel, `CappedWeight.bank, "theorem"),
  (`CappedWeight.Kernel, `CappedWeight.initial_image, "theorem"),
  (`CappedWeight.Kernel, `CappedWeight.mark, "theorem"),
  (`CappedWeight.Kernel, `CappedWeight.old, "theorem"),
  (`CappedWeight.Kernel, `CappedWeight.set3, "theorem"),
  (`CappedWeight.Kernel, `CappedWeight.set4, "theorem"),
  (`CappedWeight.Kernel, `CappedWeight.unary3, "theorem"),
  (`CappedWeight.Kernel, `CappedWeight.unary4, "theorem"),
  (`CappedWeight.Kernel, `CappedWeight.unmark, "theorem"),
  (`CappedWeight.Kernel, `CappedWeight.unset3, "theorem"),
  (`CappedWeight.Kernel, `CappedWeight.unset4, "theorem"),
  (`CappedWeight.Rows, `CappedWeight.blen, "theorem"),
  (`CappedWeight.Rows, `CappedWeight.decode_row, "theorem"),
  (`CappedWorkspace.Kernel, `CappedWorkspace.row_value, "theorem"),
  (`CarryReadyCompletion.Native, `CarryReadyCompletion.canonical_row, "theorem"),
  (`CarryWindow.Geometry, `CarryWindow.hop, "theorem"),
  (`CarryWindow.Geometry, `CarryWindow.put, "definition"),
  (`CarryWindow.Machine, `CarryWindow.liftAction, "definition"),
  (`CarryWindow.Machine, `CarryWindow.native, "definition"),
  (`CarryWindow.Machine, `CarryWindow.oldq, "definition"),
  (`CarryWindow.Raw, `CarryWindow.Closed, "definition"),
  (`CarryWindow.Raw, `CarryWindow.closed_ne, "theorem"),
  (`CarryWindow.Raw, `CarryWindow.closed_step, "theorem"),
  (`CarryWindow.Rows, `CarryWindow.native_row, "theorem"),
  (`Cursor.Machine, `Cursor.after, "definition"),
  (`Cursor.Machine, `Cursor.after0, "definition"),
  (`Cursor.Machine, `Cursor.after1, "definition"),
  (`Cursor.Machine, `Cursor.after10, "definition"),
  (`Cursor.Machine, `Cursor.after11, "definition"),
  (`Cursor.Machine, `Cursor.after12, "definition"),
  (`Cursor.Machine, `Cursor.after13, "definition"),
  (`Cursor.Machine, `Cursor.after14, "definition"),
  (`Cursor.Machine, `Cursor.after15, "definition"),
  (`Cursor.Machine, `Cursor.after16, "definition"),
  (`Cursor.Machine, `Cursor.after17, "definition"),
  (`Cursor.Machine, `Cursor.after18, "definition"),
  (`Cursor.Machine, `Cursor.after19, "definition"),
  (`Cursor.Machine, `Cursor.after2, "definition"),
  (`Cursor.Machine, `Cursor.after20, "definition"),
  (`Cursor.Machine, `Cursor.after21, "definition"),
  (`Cursor.Machine, `Cursor.after22, "definition"),
  (`Cursor.Machine, `Cursor.after23, "definition"),
  (`Cursor.Machine, `Cursor.after24, "definition"),
  (`Cursor.Machine, `Cursor.after25, "definition"),
  (`Cursor.Machine, `Cursor.after3, "definition"),
  (`Cursor.Machine, `Cursor.after4, "definition"),
  (`Cursor.Machine, `Cursor.after5, "definition"),
  (`Cursor.Machine, `Cursor.after6, "definition"),
  (`Cursor.Machine, `Cursor.after7, "definition"),
  (`Cursor.Machine, `Cursor.after8, "definition"),
  (`Cursor.Machine, `Cursor.after9, "definition"),
  (`Cursor.Machine, `Cursor.before, "definition"),
  (`Cursor.Machine, `Cursor.before0, "definition"),
  (`Cursor.Machine, `Cursor.before1, "definition"),
  (`Cursor.Machine, `Cursor.before10, "definition"),
  (`Cursor.Machine, `Cursor.before11, "definition"),
  (`Cursor.Machine, `Cursor.before2, "definition"),
  (`Cursor.Machine, `Cursor.before3, "definition"),
  (`Cursor.Machine, `Cursor.before4, "definition"),
  (`Cursor.Machine, `Cursor.before5, "definition"),
  (`Cursor.Machine, `Cursor.before6, "definition"),
  (`Cursor.Machine, `Cursor.before7, "definition"),
  (`Cursor.Machine, `Cursor.before8, "definition"),
  (`Cursor.Machine, `Cursor.before9, "definition"),
  (`Cursor.Machine, `Cursor.decode, "definition"),
  (`Cursor.Machine, `Cursor.program, "definition"),
  (`FullWeight.Checks, `FullWeight.four_rows, "theorem"),
  (`FullWeight.Checks, `FullWeight.rowTac, "definition"),
  (`FullWeight.Kernel, `FullWeight.D, "definition"),
  (`FullWeight.Kernel, `FullWeight.Frame, "definition"),
  (`FullWeight.Kernel, `FullWeight.I, "definition"),
  (`FullWeight.Kernel, `FullWeight.K, "theorem"),
  (`FullWeight.Kernel, `FullWeight.Node, "inductive"),
  (`FullWeight.Kernel, `FullWeight.Node.mk, "constructor"),
  (`FullWeight.Kernel, `FullWeight.Path, "inductive"),
  (`FullWeight.Kernel, `FullWeight.Path.append, "theorem"),
  (`FullWeight.Kernel, `FullWeight.Path.bounds, "theorem"),
  (`FullWeight.Kernel, `FullWeight.Path.cons, "constructor"),
  (`FullWeight.Kernel, `FullWeight.Path.execute, "theorem"),
  (`FullWeight.Kernel, `FullWeight.Path.first, "theorem"),
  (`FullWeight.Kernel, `FullWeight.Path.nil, "constructor"),
  (`FullWeight.Kernel, `FullWeight.atD, "theorem"),
  (`FullWeight.Kernel, `FullWeight.crossL, "theorem"),
  (`FullWeight.Kernel, `FullWeight.crossR, "theorem"),
  (`FullWeight.Kernel, `FullWeight.dec, "theorem"),
  (`FullWeight.Kernel, `FullWeight.inc, "theorem"),
  (`FullWeight.Kernel, `FullWeight.occupied, "theorem"),
  (`FullWeight.Kernel, `FullWeight.put, "definition"),
  (`FullWeight.Kernel, `FullWeight.unary, "theorem"),
  (`FullWeight.Kernel, `FullWeight.write, "theorem"),
  (`FullWeight.Loops, `FullWeight.tail, "theorem"),
  (`FullWeight.Raw, `FullWeight.cap_weight, "theorem"),
  (`FullWeight.Raw, `FullWeight.right_run, "theorem"),
  (`FullWeight.Rows, `FullWeight.add, "definition"),
  (`FullWeight.Rows, `FullWeight.addCodes, "definition"),
  (`FullWeight.Rows, `FullWeight.after, "definition"),
  (`FullWeight.Rows, `FullWeight.afterCodes, "definition"),
  (`FullWeight.Rows, `FullWeight.before, "definition"),
  (`FullWeight.Rows, `FullWeight.blen, "theorem"),
  (`FullWeight.Rows, `FullWeight.codes, "definition"),
  (`FullWeight.Rows, `FullWeight.lookup_add, "theorem"),
  (`FullWeight.Rows, `FullWeight.lookup_after, "theorem"),
  (`FullWeight.Rows, `FullWeight.middle, "definition"),
  (`FullWeight.Rows, `FullWeight.mlen, "theorem"),
  (`FullWeight.Rows, `FullWeight.power, "definition"),
  (`FullWeight.Rows, `FullWeight.powers, "theorem"),
  (`FullWeight.Rows, `FullWeight.program, "theorem"),
  (`PostWeight.Kernel, `PostWeight.Banks, "inductive"),
  (`PostWeight.Kernel, `PostWeight.Banks.mk, "constructor"),
  (`PostWeight.Kernel, `PostWeight.Banks.room, "theorem"),
  (`PostWeight.Kernel, `PostWeight.Dbound, "theorem"),
  (`PostWeight.Kernel, `PostWeight.Dstep, "theorem"),
  (`PostWeight.Kernel, `PostWeight.K, "theorem"),
  (`PostWeight.Kernel, `PostWeight.Node, "inductive"),
  (`PostWeight.Kernel, `PostWeight.Node.mk, "constructor"),
  (`PostWeight.Kernel, `PostWeight.Path, "definition"),
  (`PostWeight.Kernel, `PostWeight.Path.append, "theorem"),
  (`PostWeight.Kernel, `PostWeight.Path.execute, "theorem"),
  (`PostWeight.Kernel, `PostWeight.Path.nil, "theorem"),
  (`PostWeight.Kernel, `PostWeight.atBank, "theorem"),
  (`PostWeight.Kernel, `PostWeight.atD, "theorem"),
  (`PostWeight.Kernel, `PostWeight.crossL, "theorem"),
  (`PostWeight.Kernel, `PostWeight.crossR, "theorem"),
  (`PostWeight.Kernel, `PostWeight.hop, "theorem"),
  (`PostWeight.Kernel, `PostWeight.inc, "theorem"),
  (`PostWeight.Kernel, `PostWeight.leftI, "theorem"),
  (`PostWeight.Kernel, `PostWeight.preparation, "theorem"),
  (`PostWeight.Kernel, `PostWeight.sweepL, "theorem"),
  (`PostWeight.Kernel, `PostWeight.sweepR, "theorem"),
  (`PostWeight.Length, `PostWeight.lengthStep, "theorem"),
  (`PostWeight.Length, `PostWeight.postLength, "theorem"),
  (`PostWeight.Length, `PostWeight.seekStart, "theorem"),
  (`PostWeight.Raw, `PostWeight.ell_le, "theorem"),
  (`PostWeight.Raw, `PostWeight.join_clock, "theorem"),
  (`PostWeight.Raw, `PostWeight.seed_blank, "theorem"),
  (`PostWeight.Raw, `PostWeight.seed_occupied, "theorem"),
  (`PostWeight.Rows, `PostWeight.rowTac, "definition"),
  (`PowerDriver.Checks, `PowerDriver.rowTac, "definition"),
  (`PowerDriver.Kernel, `PowerDriver.Frame, "inductive"),
  (`PowerDriver.Kernel, `PowerDriver.Frame.banks, "theorem"),
  (`PowerDriver.Kernel, `PowerDriver.Frame.ds, "theorem"),
  (`PowerDriver.Kernel, `PowerDriver.Frame.room, "theorem"),
  (`PowerDriver.Kernel, `PowerDriver.Path.execute, "theorem"),
  (`PowerDriver.Kernel, `PowerDriver.Path.first, "theorem"),
  (`PowerDriver.Kernel, `PowerDriver.driver, "theorem"),
  (`PowerDriver.Kernel, `PowerDriver.makeFrame, "theorem"),
  (`PowerDriver.Raw, `PowerDriver.prepared_seed, "theorem"),
  (`PowerDriver.Rows, `PowerDriver.before, "definition"),
  (`PowerDriver.Rows, `PowerDriver.blen, "theorem"),
  (`PowerDriver.Rows, `PowerDriver.codes, "definition"),
  (`PowerDriver.Rows, `PowerDriver.decode_row, "theorem"),
  (`PowerDriver.Rows, `PowerDriver.flat_length, "theorem"),
  (`PowerDriver.Rows, `PowerDriver.instructions, "definition"),
  (`PowerDriver.Rows, `PowerDriver.phase_row, "theorem"),
  (`PowerDriver.Rows, `PowerDriver.power, "definition"),
  (`PowerDriver.Seed, `PowerDriver.seed_ceiling, "theorem"),
  (`RuntimeBitLength.Kernel, `RuntimeBitLength.Frame.mk, "constructor"),
  (`RuntimeBitLength.Kernel, `RuntimeBitLength.Path.execute, "theorem"),
  (`RuntimeBitLength.Kernel, `RuntimeBitLength.Path.first, "theorem"),
  (`RuntimeBitLength.Kernel, `RuntimeBitLength.entry, "theorem"),
  (`VirtualLeaf.Body, `VirtualLeaf.Trace.bound, "theorem"),
  (`VirtualLeaf.Body, `VirtualLeaf.Trace.run, "theorem"),
  (`VirtualLeaf.Body, `VirtualLeaf.append, "theorem"),
  (`VirtualLeaf.Body, `VirtualLeaf.nil, "theorem"),
  (`VirtualLeaf.Raw, `VirtualLeaf.width, "theorem"),
  (`VirtualLeaf.Transport, `VirtualLeaf.entry_val, "theorem"),
  (`VirtualLeaf.Transport, `VirtualLeaf.transport, "theorem"),
  (`VirtualReady.Kernel, `VirtualReady.Dmono, "theorem"),
  (`VirtualReady.Kernel, `VirtualReady.Frame, "inductive"),
  (`VirtualReady.Kernel, `VirtualReady.Frame.mk, "constructor"),
  (`VirtualReady.Kernel, `VirtualReady.Node, "inductive"),
  (`VirtualReady.Kernel, `VirtualReady.Node.mk, "constructor"),
  (`VirtualReady.Kernel, `VirtualReady.Path, "inductive"),
  (`VirtualReady.Kernel, `VirtualReady.Path.append, "theorem"),
  (`VirtualReady.Kernel, `VirtualReady.Path.bounds, "theorem"),
  (`VirtualReady.Kernel, `VirtualReady.Path.execute, "theorem"),
  (`VirtualReady.Kernel, `VirtualReady.Path.nil, "constructor"),
  (`VirtualReady.Kernel, `VirtualReady.aft, "definition"),
  (`VirtualReady.Kernel, `VirtualReady.cleanup_path, "theorem"),
  (`VirtualReady.Kernel, `VirtualReady.cleanup_run, "theorem"),
  (`VirtualReady.Kernel, `VirtualReady.dec_enc, "theorem"),
  (`VirtualReady.Kernel, `VirtualReady.decode_actual, "theorem"),
  (`VirtualReady.Kernel, `VirtualReady.eraseR, "theorem"),
  (`VirtualReady.Kernel, `VirtualReady.hop, "theorem"),
  (`VirtualReady.Kernel, `VirtualReady.keep, "theorem"),
  (`VirtualReady.Kernel, `VirtualReady.paint_old, "theorem"),
  (`VirtualReady.Kernel, `VirtualReady.pref_len, "theorem"),
  (`VirtualReady.Kernel, `VirtualReady.program_split, "theorem"),
  (`VirtualReady.Kernel, `VirtualReady.route_rows, "theorem"),
  (`VirtualReady.Kernel, `VirtualReady.sweepL, "theorem"),
  (`VirtualReady.Kernel, `VirtualReady.sweepR, "theorem"),
  (`VirtualReady.Raw, `VirtualReady.Base.arena, "theorem"),
  (`VirtualReady.Raw, `VirtualReady.Base.right, "theorem"),
  (`VirtualReady.Raw, `VirtualReady.Base.sep, "theorem"),
  (`VirtualReady.Raw, `VirtualReady.actual_base, "theorem"),
  (`VirtualReady.Raw, `VirtualReady.cleared_image, "theorem"),
  (`VirtualReady.Raw, `VirtualReady.computed_frame, "theorem"),
  (`VirtualReady.Raw, `VirtualReady.stage_exact, "theorem")
 ]
private def structured (text : String) : Option Name :=
  let parts := text.splitOn "."
  if parts.any String.isEmpty then none else some (parts.foldl Name.str Name.anonymous)
def lookup (env : Environment) (owner user : Name) : Except String Name := do
  let some (_,_,kind) := contracts.find? fun r => r.1 == owner && r.2.1 == user
    | throw "control/domain"
  resolve env owner user owner kind []
def select (owner user : Name) : TacticM Name := do
  match lookup (← getEnv) owner user with
  | .ok n => return n
  | .error e => throwError e
def selectText (owner ns key : String) : TacticM Name := do
  let some o := structured owner | throwError "control/owner-text"
  let some u := structured (ns ++ "." ++ key) | throwError "control/user-text"
  select o u
def bindings (owner : Name) (ns : Name) (keys : List String) : CommandElabM (List (String × Name)) := do
  let env ← getEnv
  let mut checked := []
  for key in keys do
    let some user := structured key | throwError "control/alias-text"
    let n ← match lookup env owner (ns ++ user) with
      | .ok n => pure n
      | .error e => throwError e
    checked := checked ++ [(key,n)]
  return checked
#check (resolve : Environment → Name → Name → Name → String → List Name → Except String Name)
#check (lookup : Environment → Name → Name → Except String Name)
#check (select : Name → Name → TacticM Name)
#check (selectText : String → String → String → TacticM Name)
#check (bindings : Name → Name → List String → CommandElabM (List (String × Name)))
#check (contracts : List (Name × Name × String))
#check (structured : String → Option Name)
#print axioms resolve
#print axioms lookup
#print axioms select
#print axioms selectText
#print axioms bindings
#print axioms contracts
#print axioms structured
end PartAPrivateControl
