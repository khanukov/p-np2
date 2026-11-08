import IngressAllocation.GuardedLift
namespace IngressAllocation
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command
attribute [local irreducible] UniformTM.run
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("IngressAllocation.GuardedLift","IngressAllocation","lift_guarded_prefix","guardedPrefix"),
      ("CarryReadyCompletion.Virtual","CarryReadyCompletion","virtual_cuts","virtualCuts"),
      ("VirtualLeaf.Transport","VirtualLeaf","transport","virtualTransport"),
      ("CanonicalLeaf.Rows","CanonicalLeaf","transport","canonicalTransport"),
      ("VirtualLeaf.Raw","VirtualLeaf","width","acceptedWidth")] do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,.thmInfo ci)] =>
      logInfo m!"private-term|{n}|kind=theorem|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _=>throwError "Nonunique virtual branch prefix {mod}/{key}: {found.map Prod.fst}"
set_option maxRecDepth 4000 in
private theorem virtual_consumer_heads (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (accepted : PartAEndpoint.thresholdContentWitnessRelation k a m x w=true)
    {pr : AcceptedBody.Parsed k}
    (parsed : contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr)
    (z : Nat) (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (branch : min (9+2*z+2^pr.2.n) (a+m)=a+m ∨
      (min (9+2*z+2^pr.2.n) (a+m) < a+m ∧
        a+m-min (9+2*z+2^pr.2.n) (a+m) < Cursor.Target.W k pr.2.n))
    (s : Nat)
    (_atEntry : ((IngressRepair.machine k).run s
      (initialConfig (IngressRepair.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state=VirtualLeaf.entry k)
    (atHead : ((IngressRepair.machine k).run s
      (initialConfig (IngressRepair.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).head.val=a+m+z+pr.2.n+3)
    (first : ∀ u,u < s → ((IngressRepair.machine k).run u
      (initialConfig (IngressRepair.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state ≠ VirtualLeaf.entry k)
    (oldHeads : Footprint (AllArityCursor.machine k) (C:=FixedRawLengthFence.allocation (pairLength a m))
      (encodePair x w) s (12*(pairLength a m+1)^2)) :
    Footprint (BodyIngress.machine k) (C:=FixedRawLengthFence.allocation (pairLength a m))
      (encodePair x w) (s+5) (12*(pairLength a m+1)^2) := by
  let R:=pairLength a m;let B:=FixedRawLengthFence.allocation R
  let old:=initialConfig (IngressRepair.machine k) B (encodePair x w)
  let base:=initialConfig (AllArityCursor.machine k) B (encodePair x w)
  let can:=initialConfig (CanonicalLeaf.machine k) B (encodePair x w)
  let body:=initialConfig (BodyIngress.machine k) B (encodePair x w)
  have repair (u : Nat) : (IngressRepair.machine k).run u old=(AllArityCursor.machine k).run u base:=
    IngressRepair.accepted_transport k x w accepted u
  have vt:=virtualTransport old (t:=s) first
  have ct:=canonicalTransport (VirtualLeaf.config k old) (t:=s) (by
    intro u hu
    rw [vt u (Nat.le_of_lt hu)]
    exact ((IngressRepair.machine k).run u old).state.isLt)
  have canEq (u : Nat) (hu : u ≤ s) : (CanonicalLeaf.machine k).run u can=
      VirtualLeaf.config k ((AllArityCursor.machine k).run u base):=by
    exact (ct u hu).trans ((vt u hu).trans (congrArg (VirtualLeaf.config k) (repair u)))
  have cuts:=virtualCuts k x w accepted pr parsed z gamma branch
  have readyOld (u : Nat) (hu : u < s) : ((AllArityCursor.machine k).run u base).state ≠ VirtualLeaf.entry k:=by
    rw [← repair u]
    exact first u hu
  have avoid (u : Nat) (hu : u < s) (j : Nat) (hj : j=430 ∨ j=613) :
      ((AllArityCursor.machine k).run u base).state ≠ IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.q k (j+93*k)):=by
    intro bad
    have mapped : ((CanonicalLeaf.machine k).run u can).state=VirtualLeaf.embed k
        (IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.q k (j+93*k))):=by
      rw [canEq u (Nat.le_of_lt hu)]
      exact congrArg (VirtualLeaf.embed k) bad
    rcases hj with rfl|rfl
    · exact (cuts u).1 mapped
    · exact (cuts u).2 mapped
  have tx:=guardedPrefix k x w accepted s readyOld avoid
  have prefixHeads (u : Nat) (hu : u ≤ s) : ((BodyIngress.machine k).run u body).head.val ≤ 12*(R+1)^2:=by
    rw [tx u hu]
    exact oldHeads u hu
  have head : ((BodyIngress.machine k).run s body).head.val=a+m+z+pr.2.n+3:=by
    rw [tx s le_rfl]
    change ((AllArityCursor.machine k).run s base).head.val=_
    rw [← repair s]
    exact atHead
  have width:=acceptedWidth x w accepted parsed
  have pair : a+m ≤ R:=by dsimp only [R,pairLength];omega
  have gammaBound:=((FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 z gamma).1
  have bound : a+m+z+pr.2.n+3+5 ≤ 12*(R+1)^2:=by
    nlinarith only [pair,width,gammaBound,Nat.zero_le R,Nat.zero_le (R^2)]
  intro u hu
  by_cases early : u ≤ s
  · exact prefixHeads u early
  · rw [show u=s+(u-s) by omega,UniformTM.run_add]
    have speed:=(BodyIngress.machine k).run_head_le (steps:=u-s) ((BodyIngress.machine k).run s body)
    rw [head] at speed
    exact speed.trans (by change a+m+z+pr.2.n+3+(u-s) ≤ 12*(R+1)^2;omega)
end IngressAllocation
