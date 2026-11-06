import Complexity.PrivateInterfaceLookupResolvedControl
open Lean Elab Tactic
namespace PartAPrivateLeaf
/- Finite literal source-backed domain. Metadata identity, not donor full-signature equality. -/
private def contracts : List (Name × Name × String) := [
  (`VirtualLeaf.Machine, `VirtualLeaf.rows, "definition"),
  (`VirtualReady.Kernel, `VirtualReady.codes, "definition"),
  (`VirtualReady.Kernel, `VirtualReady.aft, "definition"),
  (`VirtualReady.Kernel, `VirtualReady.sym, "definition"),
  (`VirtualReady.Kernel, `VirtualReady.enc, "definition"),
  (`VirtualReady.Kernel, `VirtualReady.mov, "definition"),
  (`VirtualLeaf.Transport, `VirtualLeaf.keep, "theorem"),
  (`VirtualLeaf.Transport, `VirtualLeaf.extra_row, "theorem"),
  (`VirtualLeaf.Transport, `VirtualLeaf.entry_ne, "theorem"),
  (`VirtualLeaf.Transport, `VirtualLeaf.first_ready, "theorem"),
  (`VirtualLeaf.Transport, `VirtualLeaf.transport, "theorem"),
  (`VirtualLeaf.Transport, `VirtualLeaf.avoids, "theorem"),
  (`VirtualLeaf.Transport, `VirtualLeaf.entry_val, "theorem"),
  (`VirtualLeaf.Body, `VirtualLeaf.single, "theorem"),
  (`VirtualLeaf.Body, `VirtualLeaf.append, "theorem"),
  (`VirtualLeaf.Body, `VirtualLeaf.native, "theorem"),
  (`VirtualLeaf.Body, `VirtualLeaf.extra_ne, "theorem"),
  (`VirtualLeaf.Body, `VirtualLeaf.Trace.run, "theorem"),
  (`VirtualLeaf.Body, `VirtualLeaf.Trace.bound, "theorem"),
  (`VirtualLeaf.Body, `VirtualLeaf.Trace, "inductive"),
  (`VirtualLeaf.Source, `VirtualLeaf.virtual_source, "theorem"),
  (`VirtualLeaf.Raw, `VirtualLeaf.image_before, "theorem"),
  (`VirtualLeaf.Raw, `VirtualLeaf.width, "theorem"),
  (`CanonicalLeaf.Machine, `CanonicalLeaf.rows, "definition"),
  (`CanonicalLeaf.Rows, `CanonicalLeaf.native, "theorem"),
  (`CanonicalLeaf.Rows, `CanonicalLeaf.disjoint, "theorem"),
  (`CanonicalLeaf.Rows, `CanonicalLeaf.base_end, "theorem"),
  (`CanonicalLeaf.Rows, `CanonicalLeaf.transport, "theorem"),
  (`CarryWindow.Machine, `CarryWindow.oldq, "definition"),
  (`CarryWindow.Machine, `CarryWindow.rows, "definition"),
  (`CarryWindow.Machine, `CarryWindow.native, "definition"),
  (`CarryWindow.Machine, `CarryWindow.extend, "definition"),
  (`CarryWindow.Machine, `CarryWindow.liftAction, "definition")]
def key (s : String) : Name := (s.splitOn ".").foldl Name.str .anonymous
def lookup (env : Environment) (owner user : Name) : Except String Name := do
  let some row := contracts.find? (fun r => r.1 == owner && r.2.1 == user) | throw "leaf/domain"
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
end PartAPrivateLeaf
