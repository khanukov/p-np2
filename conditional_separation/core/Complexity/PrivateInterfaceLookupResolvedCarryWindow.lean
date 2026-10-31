import Complexity.PrivateInterfaceLookupResolvedControl
open Lean Elab Tactic
namespace PartAPrivateCarryWindow
/- Finite source-backed metadata identity; not independently expected donor full signature. -/
private def contracts : List (Name × Name × String) := [
  (`VirtualLeaf.Body, `VirtualLeaf.nil, "theorem"),
  (`VirtualLeaf.Body, `VirtualLeaf.single, "theorem"),
  (`VirtualLeaf.Body, `VirtualLeaf.append, "theorem"),
  (`VirtualLeaf.Body, `VirtualLeaf.sweepL, "theorem"),
  (`VirtualLeaf.Body, `VirtualLeaf.sweepR, "theorem"),
  (`VirtualLeaf.Body, `VirtualLeaf.Trace.run, "theorem"),
  (`VirtualLeaf.Body, `VirtualLeaf.Trace.bound, "theorem"),
  (`VirtualLeaf.Body, `VirtualLeaf.Trace, "inductive"),
  (`CarryWindow.Rows, `CarryWindow.native_row, "theorem"),
  (`CarryWindow.Machine, `CarryWindow.native, "definition"),
  (`CarryWindow.Geometry, `CarryWindow.C, "definition"),
  (`CarryWindow.Geometry, `CarryWindow.D, "definition"),
  (`CarryWindow.Geometry, `CarryWindow.A, "definition"),
  (`CarryWindow.Geometry, `CarryWindow.value, "definition"),
  (`CarryWindow.Geometry, `CarryWindow.put, "definition"),
  (`CarryWindow.Geometry, `CarryWindow.dest, "definition"),
  (`CarryWindow.Geometry, `CarryWindow.atD, "theorem"),
  (`CarryWindow.Geometry, `CarryWindow.atBank, "theorem"),
  (`CarryWindow.Geometry, `CarryWindow.occupied, "theorem"),
  (`CarryWindow.Geometry, `CarryWindow.set0, "theorem"),
  (`CarryWindow.Geometry, `CarryWindow.take0, "theorem"),
  (`CarryWindow.Geometry, `CarryWindow.take3, "theorem"),
  (`CarryWindow.Geometry, `CarryWindow.clear0, "theorem"),
  (`CarryWindow.Geometry, `CarryWindow.hop, "theorem"),
  (`CarryWindow.Geometry, `CarryWindow.keep, "theorem"),
  (`CarryWindow.Geometry, `CarryWindow.Banks, "inductive"),
  (`CarryWindow.Geometry, `CarryWindow.Banks.mk, "constructor"),
  (`CarryWindow.Body, `CarryWindow.carry, "theorem"),
  (`CarryWindow.Body, `CarryWindow.actual_row, "theorem"),
  (`CarryWindow.Body, `CarryWindow.base_dead, "theorem"),
  (`CarryWindow.Body, `CarryWindow.shift_dest, "theorem"),
  (`CarryWindow.Body, `CarryWindow.code0, "definition"),
  (`CarryWindow.Body, `CarryWindow.deadBase, "definition"),
  (`CarryWindow.Body, `CarryWindow.action, "definition"),
  (`VirtualLeaf.Transport, `VirtualLeaf.entry_val, "theorem"),
  (`CarryWindow.Transport, `CarryWindow.transport, "theorem"),
  (`Cursor.Machine, `Cursor.after, "definition"),
  (`Cursor.Machine, `Cursor.after0, "definition"),
  (`Cursor.Machine, `Cursor.after1, "definition"),
  (`Cursor.Machine, `Cursor.after2, "definition"),
  (`Cursor.Machine, `Cursor.after3, "definition"),
  (`Cursor.Machine, `Cursor.after4, "definition"),
  (`Cursor.Machine, `Cursor.after5, "definition"),
  (`Cursor.Machine, `Cursor.after6, "definition"),
  (`Cursor.Machine, `Cursor.after7, "definition"),
  (`Cursor.Machine, `Cursor.after8, "definition"),
  (`Cursor.Machine, `Cursor.after9, "definition"),
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
  (`Cursor.Machine, `Cursor.after20, "definition"),
  (`Cursor.Machine, `Cursor.after21, "definition"),
  (`Cursor.Machine, `Cursor.after22, "definition"),
  (`Cursor.Machine, `Cursor.after23, "definition"),
  (`Cursor.Machine, `Cursor.after24, "definition"),
  (`Cursor.Machine, `Cursor.after25, "definition")]
def key (s : String) : Name := (s.splitOn ".").foldl Name.str .anonymous
def lookup (env : Environment) (owner user : Name) : Except String Name := do
  let some row := contracts.find? (fun r => r.1 == owner && r.2.1 == user) | throw "carry-window/domain"
  PartAPrivateControl.resolve env owner user owner row.2.2 []
def batch (env : Environment) (rows : List (Name × Name)) : Except String (List Name) :=
  rows.mapM fun (owner,user) => lookup env owner user
def select (owner user : Name) : TacticM Name := do
  ofExcept (lookup (← getEnv) owner user)
#check (key : String → Name)
#check (lookup : Environment → Name → Name → Except String Name)
#check (batch : Environment → List (Name × Name) → Except String (List Name))
#check (select : Name → Name → TacticM Name)
#print axioms key
#print axioms lookup
#print axioms batch
#print axioms select
end PartAPrivateCarryWindow
