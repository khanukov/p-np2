import NormalFinalClosure.Prefix
import PhysicalCallerClosure.CopyKernel
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
private def exactSupport (owner : Name) (ns : Name) (leaf kind : String) : TacticM Unit := do
  let e←getEnv
  let suffix:="."++ns.toString++"."++leaf
  let found:=e.constants.toList.filter fun (n,_)=>
    n.toString.startsWith ("_private."++owner.toString++".") && n.toString.endsWith suffix
  let [(n,ci)]:=found | throwError "Nonunique immutable support {owner}/{ns}/{leaf}"
  let actual:=match ci with|.thmInfo _=>"theorem"|.defnInfo _=>"definition"|.inductInfo _=>"inductive"|.ctorInfo _=>"constructor"|_=>"other"
  unless actual==kind do throwError "Wrong immutable support kind {n}"
  let some i:=e.getModuleIdxFor? n | throwError "Missing immutable owner"
  unless i.toNat < e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong immutable owner"
  logInfo m!"normal-exact-support|{owner}|{kind}|{n}|{ci.type}"
  closeMainGoal `exactSupport (mkConst n (ci.levelParams.map Level.param))
run_cmd do
  let e←getEnv
  for (owner,ns,leaves) in [
    (`PhysicalCallerClosure.Engine,`PhysicalCallerClosure,["Node","Path","Grid","Unary","ClearRows","DecRows","IncRows","RouteR","RouteL"]),
    (`PhysicalCallerClosure.UnaryCopy,`PhysicalCallerClosure,["field"])] do
    for leaf in leaves do
      let found:=e.constants.toList.filter fun (n,_)=>
        n.toString.startsWith ("_private."++owner.toString++".") && n.toString.endsWith ("."++ns.toString++"."++leaf)
      let [(n,ci)]:=found | throwError "Nonunique exact support {owner}/{leaf}"
      let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
      unless i.toNat < e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong owner"
      logInfo m!"normal-open-support|{owner}|{n}|{ci.type}"
      modifyScope fun s=>{s with openDecls:=.explicit (Name.str .anonymous leaf) n::s.openDecls}
private abbrev node : {M : UniformTM} → Fin M.stateCount → Nat → (Nat → Option Bool) → Node M := by
  run_tac exactSupport `PhysicalCallerClosure.Engine `PhysicalCallerClosure "Node.mk" "constructor"
private theorem append : ∀ {M : UniformTM} {Safe : Fin M.stateCount → Prop}
    {P t u : Nat} {a b c : Node M},
    Path M Safe P t a b → Path M Safe P u b c → Path M Safe P (t+u) a c := by
  run_tac exactSupport `PhysicalCallerClosure.Engine `PhysicalCallerClosure "Path.append" "theorem"
private theorem clearRun : ∀ {M : UniformTM} {Safe : Fin M.stateCount → Prop}
    {D : Nat → Nat} {T : Nat → Option Bool} {P j : Nat} {b : Bool} {start out : Fin M.stateCount},
    Grid D T → j < 13 → D 13 ≤ P → ClearRows (Safe:=Safe) j b start out →
    Path M Safe P (2*(D (j+1)-D 0+j)+2) (node start (D 0) T)
      (node out (D 0) (fun i=>if D j+1 ≤ i ∧ i < D j+1+(D (j+1)-D j-1) then some b else T i)) := by
  run_tac exactSupport `PhysicalCallerClosure.Engine `PhysicalCallerClosure "clear_run" "theorem"
private theorem decZero : ∀ {M : UniformTM} {Safe : Fin M.stateCount → Prop}
    {D : Nat → Nat} {T : Nat → Option Bool} {j w P : Nat} {start zero pos : Fin M.stateCount},
    Grid D T → j < 13 → D 13 ≤ P → D (j+1)=D j+w+1 → Unary D T j 0 →
    DecRows (Safe:=Safe) j start zero pos →
    Path M Safe P (2*(D j-D 0+j)+3) (node start (D 0) T) (node zero (D 0) T) := by
  run_tac exactSupport `PhysicalCallerClosure.Engine `PhysicalCallerClosure "dec_zero" "theorem"
private theorem decPositive : ∀ {M : UniformTM} {Safe : Fin M.stateCount → Prop}
    {D : Nat → Nat} {T : Nat → Option Bool} {j w v P : Nat} {start zero pos : Fin M.stateCount},
    Grid D T → j < 13 → D 13 ≤ P → D (j+1)=D j+w+1 → Unary D T j v →
    0 < v → v ≤ w → DecRows (Safe:=Safe) j start zero pos →
    Path M Safe P (2*(D j-D 0+j)+2*v+3) (node start (D 0) T)
      (node pos (D 0) (fun i=>if i=D j+v then some false else T i)) := by
  run_tac exactSupport `PhysicalCallerClosure.Engine `PhysicalCallerClosure "dec_positive" "theorem"
private theorem incSuccess : ∀ {M : UniformTM} {Safe : Fin M.stateCount → Prop}
    {D : Nat → Nat} {T : Nat → Option Bool} {j w v P : Nat} {start out : Fin M.stateCount},
    Grid D T → j < 13 → D 13 ≤ P → D (j+1)=D j+w+1 → Unary D T j v →
    v < w → IncRows (Safe:=Safe) j start out →
    Path M Safe P (2*(D j-D 0+j)+2*v+3) (node start (D 0) T)
      (node out (D 0) (fun i=>if i=D j+v+1 then some true else T i)) := by
  run_tac exactSupport `PhysicalCallerClosure.Engine `PhysicalCallerClosure "inc_success" "theorem"
private theorem fieldSelf : ∀ {T : Nat → Option Bool} {D : Nat → Nat} {j v : Nat},
    Unary D T j v → field T D j v=T := by
  run_tac exactSupport `PhysicalCallerClosure.UnaryCopy `PhysicalCallerClosure "field_self" "theorem"
private theorem fieldGrid : ∀ {D : Nat → Nat} {T : Nat → Option Bool},
    Grid D T → ∀ j v,j < 13 → Grid D (field T D j v) := by
  run_tac exactSupport `PhysicalCallerClosure.UnaryCopy `PhysicalCallerClosure "field_grid" "theorem"
private theorem fieldOther : ∀ {D : Nat → Nat} {T : Nat → Option Bool} {j k v w : Nat},
    Grid D T → j < 13 → k < 13 → j≠k → Unary D T k w → Unary D (field T D j v) k w := by
  run_tac exactSupport `PhysicalCallerClosure.UnaryCopy `PhysicalCallerClosure "field_other" "theorem"
end NormalFinalClosure
