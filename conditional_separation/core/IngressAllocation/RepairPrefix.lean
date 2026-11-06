import IngressAllocation.EarlyLift
namespace IngressAllocation
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
attribute [local irreducible] UniformTM.run
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("VirtualLeaf.Transport","VirtualLeaf","transport","virtualTransport"),
      ("VirtualLeaf.Transport","VirtualLeaf","entry_val","entryVal"),
      ("CanonicalLeaf.Rows","CanonicalLeaf","transport","canonicalTransport"),
      ("CarryWindow.Transport","CarryWindow","transport","carryTransport"),
      ("CarryWindow.Transport","CarryWindow","cut_val","cutVal")] do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,.thmInfo ci)] =>
      logInfo m!"private-term|{n}|kind=theorem|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _=>throwError "Nonunique repaired early prefix {mod}/{key}: {found.map Prod.fst}"
private def repairEmbed {k N B : Nat} (c : Config (IngressRepair.machine k).stateCount N B) :
    Config (BodyIngress.machine k).stateCount N B:=BodyIngress.config k (CarryWindow.config k (VirtualLeaf.config k c))
set_option maxRecDepth 4000 in
private theorem repair_low_prefix {k N B t : Nat} (c : Config (IngressRepair.machine k).stateCount N B)
    (low : ∀ u,u < t → ((IngressRepair.machine k).run u c).state.val < 139) :
    ∀ u,u ≤ t → (BodyIngress.machine k).run u (repairEmbed c)=repairEmbed ((IngressRepair.machine k).run u c):=by
  let virtual:=VirtualLeaf.config k c
  let carry:=CarryWindow.config k virtual
  have vt:=virtualTransport c (t:=t) (by
    intro u hu bad
    have bound:=low u hu
    rw [bad,entryVal] at bound
    omega)
  have ct:=canonicalTransport virtual (t:=t) (by
    intro u hu
    rw [vt u (Nat.le_of_lt hu)]
    exact ((IngressRepair.machine k).run u c).state.isLt)
  have canLow (u : Nat) (hu : u < t) : ((CanonicalLeaf.machine k).run u virtual).state.val < 139:=by
    rw [ct u (Nat.le_of_lt hu),vt u (Nat.le_of_lt hu)]
    exact low u hu
  have kt:=carryTransport virtual (t:=t) (by
    intro u hu
    constructor
    all_goals
      intro bad
      have bound:=canLow u hu
      have eq:=congrArg Fin.val bad
      rw [cutVal k _ (by unfold Cursor.stateCount;omega)] at eq
      omega)
  have bt:=BodyIngress.transport carry (t:=t) (by
    intro u hu bad
    have bound : ((CarryWindow.machine k).run u carry).state.val < 139:=by
      rw [kt u (Nat.le_of_lt hu)]
      exact canLow u hu
    have eq:=congrArg Fin.val bad
    change _=(CanonicalLeaf.machine k).stateCount+24 at eq
    have big : 139 ≤ (CanonicalLeaf.machine k).stateCount:=by
      change 139 ≤ 288+Cursor.stateCount k+8
      omega
    omega)
  intro u hu
  dsimp only [repairEmbed]
  rw [bt u hu,kt u hu,ct u hu,vt u hu]
end IngressAllocation
