import Complexity.PrivateInterfaceLookupResolvedControl
/- Finite source-backed metadata identity, not full signature equality. Current env
   only; no enumeration/cache. Batch validation is pure and retains duplicates/order. -/
open Lean Elab Tactic
namespace PartAPrivateRuntime
private def contracts : List (Name × Name × String) := [
  (`Cursor.Proof, `Cursor.eof_kernel, "theorem"),
  (`Stream.Kernel, `Stream.current_value, "theorem"),
  (`Stream.Kernel, `Stream.last_overflow, "theorem"),
  (`Stream.Kernel, `Stream.iter_succ, "theorem"),
  (`SuffixCap.Kernel, `SuffixCap.Frame, "inductive"),
  (`SuffixCap.Kernel, `SuffixCap.Frame.mk, "constructor"),
  (`SuffixCap.Kernel, `SuffixCap.base, "definition"),
  (`SuffixCap.Kernel, `SuffixCap.keep, "theorem"),
  (`SuffixCap.Kernel, `SuffixCap.hop, "theorem"),
  (`SuffixCap.Kernel, `SuffixCap.count_iteration, "theorem"),
  (`SuffixCap.Kernel, `SuffixCap.small_mod, "theorem"),
  (`SuffixCap.Kernel, `SuffixCap.Path.append, "theorem"),
  (`SuffixCap.Kernel, `SuffixCap.Path.first, "theorem"),
  (`SuffixCap.Raw, `SuffixCap.raw_prefix, "theorem"),
  (`AllArityCounted.Runtime, `AllArityCounted.actual_cells, "theorem"),
  (`AllArityCounted.Runtime, `AllArityCounted.Cells.arena, "theorem"),
  (`AllArityCounted.Runtime, `AllArityCounted.Cells.source, "theorem"),
  (`AllArityCounted.Runtime, `AllArityCounted.Cells.eof, "theorem"),
  (`AllArityCounted.Runtime, `AllArityCounted.Cells.reg, "theorem"),
  (`AllArityCounted.Runtime, `AllArityCounted.Cells.sep, "theorem"),
  (`AllArityCounted.Runtime, `AllArityCounted.Cells.assn, "theorem"),
  (`AllArityCounted.Runtime, `AllArityCounted.Cells.right, "theorem"),
  (`AllArityCounted.Runtime, `AllArityCounted.Cells.marks, "theorem"),
  (`AllArityCounted.Runtime, `AllArityCounted.Cells.gap, "theorem"),
  (`AllArityCounted.Runtime, `AllArityCounted.Cells.fence, "theorem"),
  (`CappedWorkspace.Raw, `CappedWorkspace.suffix_bound, "theorem"),
  (`FullWeight.Kernel, `FullWeight.Path.nil, "constructor"),
  (`FullWeight.Kernel, `FullWeight.Path, "inductive"),
  (`FullWeight.Kernel, `FullWeight.Path.append, "theorem"),
  (`FullWeight.Kernel, `FullWeight.K, "theorem"),
  (`FullWeight.Kernel, `FullWeight.Frame, "definition"),
  (`FullWeight.Kernel, `FullWeight.D, "definition"),
  (`FullWeight.Kernel, `FullWeight.atD, "theorem"),
  (`FullWeight.Body, `FullWeight.N, "definition"),
  (`FullWeight.Body, `FullWeight.J, "definition"),
  (`FullWeight.Body, `FullWeight.V, "definition"),
  (`FullWeight.Body, `FullWeight.incAdd, "theorem"),
  (`FullWeight.Body, `FullWeight.addCap, "theorem"),
  (`FullWeight.Body, `FullWeight.rowTac, "definition"),
  (`FullWeight.Body, `FullWeight.put3true, "theorem"),
  (`FullWeight.Body, `FullWeight.decRest, "theorem"),
  (`FullWeight.Body, `FullWeight.put5false, "theorem"),
  (`FullWeight.Body, `FullWeight.route398, "theorem"),
  (`FullWeight.Body, `FullWeight.incRest, "theorem"),
  (`FullWeight.Body, `FullWeight.route406, "theorem"),
  (`FullWeight.Body, `FullWeight.incFour, "theorem"),
  (`FullWeight.Body, `FullWeight.route336, "theorem"),
  (`FullWeight.Body, `FullWeight.route344, "theorem"),
  (`FullWeight.Body, `FullWeight.route352, "theorem"),
  (`FullWeight.Body, `FullWeight.route360, "theorem"),
  (`FullWeight.Body, `FullWeight.decInner, "theorem"),
  (`FullWeight.Body, `FullWeight.route390, "theorem"),
  (`FullWeight.Body, `FullWeight.route416, "theorem"),
  (`FullWeight.Body, `FullWeight.route374, "theorem"),
  (`FullWeight.Body, `FullWeight.incOut, "theorem"),
  (`FullWeight.Body, `FullWeight.put4true, "theorem"),
  (`FullWeight.Body, `FullWeight.route380, "theorem"),
  (`FullWeight.Body, `FullWeight.incTemp, "theorem"),
  (`FullWeight.Body, `FullWeight.put5true, "theorem"),
  (`FullWeight.Body, `FullWeight.route386, "theorem"),
  (`FullWeight.Body, `FullWeight.route422, "theorem"),
  (`FullWeight.Body, `FullWeight.put3false, "theorem"),
  (`FullWeight.Body, `FullWeight.decOuter, "theorem"),
  (`FullWeight.Body, `FullWeight.put2false, "theorem"),
  (`FullWeight.Body, `FullWeight.route368, "theorem"),
  (`FullWeight.Body, `FullWeight.put2true, "theorem"),
  (`FullWeight.Body, `FullWeight.route330, "theorem")]
def lookup (env : Environment) (owner user : Name) : Except String Name := do
  let some row := contracts.find? (fun r => r.1 == owner && r.2.1 == user)
    | throw "runtime/domain"
  PartAPrivateControl.resolve env owner user owner row.2.2 []
def batch (env : Environment) (rows : List (Name × Name)) : Except String (List Name) :=
  rows.mapM fun (owner,user) => lookup env owner user
def select (owner user : Name) : TacticM Name := do
  ofExcept (lookup (← getEnv) owner user)
#check (lookup : Environment → Name → Name → Except String Name)
#check (batch : Environment → List (Name × Name) → Except String (List Name))
#check (select : Name → Name → TacticM Name)
#print axioms lookup
#print axioms batch
#print axioms select
end PartAPrivateRuntime
