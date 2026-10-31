import IngressAllocation.Producer
import IngressAllocation.Endpoint
namespace IngressAllocation
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion PairEncoding Lean Elab Command
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("VirtualLeaf.Transport","VirtualLeaf","transport","virtualTransport"),
      ("VirtualLeaf.Transport","VirtualLeaf","entry_val","virtualEntryVal"),
      ("CanonicalLeaf.Rows","CanonicalLeaf","transport","canonicalTransport"),
      ("CarryWindow.Transport","CarryWindow","transport","carryTransport"),
      ("CarryWindow.Transport","CarryWindow","cut_val","cutVal")] do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,.thmInfo ci)] =>
      logInfo m!"private-term|{n}|kind=theorem|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _=>throwError "Nonunique literal prefix theorem {mod}/{key}: {found.map Prod.fst}"
private def earlyEmbed {k N B : Nat} (c : Config (IngressRepair.machine k).stateCount N B) :
    Config (BodyIngress.machine k).stateCount N B :=
  BodyIngress.config k (CarryWindow.config k (VirtualLeaf.config k c))
/- Entire every-time prefix transport, before entering any Cursor arithmetic or live cut. -/
set_option maxRecDepth 4000 in
private theorem lift_early_prefix (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (accepted : PartAEndpoint.thresholdContentWitnessRelation k a m x w=true) (t : Nat)
    (low : ∀ u,u ≤ t → ((AllArityCursor.machine k).run u
      (initialConfig (AllArityCursor.machine k) (FixedRawLengthFence.allocation (pairLength a m))
        (encodePair x w))).state.val ≤ 617) :
    ∀ u,u ≤ t → (BodyIngress.machine k).run u
      (initialConfig (BodyIngress.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))=
      earlyEmbed (k:=k) ((AllArityCursor.machine k).run u
        (initialConfig (AllArityCursor.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))) := by
  let B:=FixedRawLengthFence.allocation (pairLength a m)
  let repaired:=initialConfig (IngressRepair.machine k) B (encodePair x w)
  let virtual:=VirtualLeaf.config k repaired
  let carry:=CarryWindow.config k virtual
  have repair (u : Nat) : (IngressRepair.machine k).run u repaired=(AllArityCursor.machine k).run u
      (initialConfig (AllArityCursor.machine k) B (encodePair x w)):=IngressRepair.accepted_transport k x w accepted u
  have repairedLow (u : Nat) (hu : u ≤ t) : ((IngressRepair.machine k).run u repaired).state.val ≤ 617 := by
    rw [repair];exact low u hu
  have virtualTx:=virtualTransport repaired (t:=t) (by
    intro u hu bad
    have bound:=repairedLow u (Nat.le_of_lt hu)
    have eq:=congrArg Fin.val bad
    rw [virtualEntryVal k] at eq
    omega)
  have canonicalTx:=canonicalTransport virtual (t:=t) (by
    intro u hu
    rw [virtualTx u (Nat.le_of_lt hu)]
    change ((IngressRepair.machine k).run u repaired).state.val < (IngressRepair.machine k).stateCount
    have bound:=repairedLow u (Nat.le_of_lt hu)
    change _ < 288+Cursor.stateCount k
    unfold Cursor.stateCount
    omega)
  have canonicalLow (u : Nat) (hu : u ≤ t) : ((CanonicalLeaf.machine k).run u virtual).state.val ≤ 617 := by
    rw [canonicalTx u hu,virtualTx u hu]
    exact repairedLow u hu
  have carryTx:=carryTransport virtual (t:=t) (by
    intro u hu
    constructor
    all_goals
      intro bad
      have bound:=canonicalLow u (Nat.le_of_lt hu)
      have eq:=congrArg Fin.val bad
    · rw [cutVal k 430 (by unfold Cursor.stateCount;omega)] at eq
      omega
    · rw [cutVal k 613 (by unfold Cursor.stateCount;omega)] at eq
      omega)
  have bodyTx:=BodyIngress.transport carry (t:=t) (by
    intro u hu bad
    have bound : ((CarryWindow.machine k).run u carry).state.val ≤ 617 := by
      rw [carryTx u (Nat.le_of_lt hu)]
      exact canonicalLow u (Nat.le_of_lt hu)
    have eq:=congrArg Fin.val bad
    change _=(CanonicalLeaf.machine k).stateCount+24 at eq
    have base : 617 ≤ (CanonicalLeaf.machine k).stateCount := by
      change 617 ≤ 288+Cursor.stateCount k+8
      unfold Cursor.stateCount
      omega
    omega)
  intro u hu
  have initial : BodyIngress.config k carry=initialConfig (BodyIngress.machine k) B (encodePair x w):=rfl
  rw [← initial,bodyTx u hu,carryTx u hu,canonicalTx u hu,virtualTx u hu,repair u]
  rfl
end IngressAllocation
