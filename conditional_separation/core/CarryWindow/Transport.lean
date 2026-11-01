import CarryWindow.Rows
import Complexity.PrivateInterfaceLookupResolvedLeaf
namespace CarryWindow
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion PairEncoding Lean Elab Command
set_option maxRecDepth 10000
attribute [local irreducible] UniformTM.run
run_cmd do
  let rows := [("VirtualLeaf.Transport","VirtualLeaf","transport","virtualTransport"),
      ("CanonicalLeaf.Rows","CanonicalLeaf","transport","canonicalTransport"),
      ("VirtualLeaf.Transport","VirtualLeaf","entry_val","entry_val")]
  let validated ← ofExcept (PartAPrivateLeaf.batch (← getEnv) (rows.map fun (o,ns,s,_) => (PartAPrivateLeaf.key o, PartAPrivateLeaf.key (ns++"."++s))))
  for ((mod,ns,s,key),target) in rows.zip validated do
    let _ := (mod,ns,s)
    let names := [target]
    logInfo m!"private-term|{names.head!}"
    modifyScope fun st => {st with openDecls:=.explicit (Name.str Name.anonymous key) names.head! :: st.openDecls}
private def cut (k i : Nat) : Fin (CanonicalLeaf.machine k).stateCount :=
  VirtualLeaf.embed k (IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.q k (i+93*k)))
private theorem step_lift {k N B : Nat} (c : Config (CanonicalLeaf.machine k).stateCount N B)
    (a : c.state ≠ cut k 430) (b : c.state ≠ cut k 613) :
    (machine k).stepConfig (config k c)=config k ((CanonicalLeaf.machine k).stepConfig c) := by
  unfold UniformTM.stepConfig
  dsimp only [config]
  rw [table_delta,if_neg (by exact fun h => a h.1),if_neg (by exact fun h => b h.1)]
private theorem transport {k N B t : Nat} (c : Config (CanonicalLeaf.machine k).stateCount N B)
    (safe : ∀ u, u<t → ((CanonicalLeaf.machine k).run u c).state ≠ cut k 430 ∧
      ((CanonicalLeaf.machine k).run u c).state ≠ cut k 613) :
    ∀ u, u≤t → (machine k).run u (config k c)=config k ((CanonicalLeaf.machine k).run u c) := by
  intro u hu
  induction u with
  | zero => rw [UniformTM.run,UniformTM.run]
  | succ u ih =>
    rw [UniformTM.run,ih (by omega),step_lift _ (safe u (by omega)).1 (safe u (by omega)).2,UniformTM.run]
private theorem cut_val (k i : Nat) (hi : i+93*k < Cursor.stateCount k) :
    (cut k i).val=288+i+93*k := by
  change 288+(i+93*k)%Cursor.stateCount k=288+i+93*k
  rw [Nat.mod_eq_of_lt hi]; omega
/-- Universal reviewed missing-FIRST-payload domain still reaches literal reject. -/
theorem missing_payload (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m) (z : Nat)
    (tag : FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (pos : 0<z) (short : a+m=9+z) :
    ∃ t, t≤128*(pairLength a m+1)^2 ∧
      ((machine k).run t (initialConfig (machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state=(machine k).reject ∧
      PartAEndpoint.thresholdContentWitnessRelation k a m x w=false := by
  obtain ⟨t,ht,done,prior,_safe,negative⟩:=IngressRepair.absent_first_payload k x w z tag gamma pos short
  let old:=initialConfig (IngressRepair.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)
  have noEntry (u : Nat) (hu : u<t) : ((IngressRepair.machine k).run u old).state ≠ VirtualLeaf.entry k := by
    intro bad; have bound:=prior u hu; have eq:=congrArg Fin.val bad
    rw [entry_val] at eq
    change ((IngressRepair.machine k).run u old).state.val < 139 at bound
    omega
  have vt:=virtualTransport old noEntry
  have ct:=canonicalTransport (VirtualLeaf.config k old) (t:=t) (by
    intro u hu
    rw [vt u (by omega)]
    have bound:=prior u hu
    change ((IngressRepair.machine k).run u old).state.val < (IngressRepair.machine k).stateCount
    have room : 139 ≤ (IngressRepair.machine k).stateCount := by change 139 ≤ 288+Cursor.stateCount k; omega
    omega)
  let base:=initialConfig (CanonicalLeaf.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)
  have eq (u : Nat) (hu : u≤t) :
      (CanonicalLeaf.machine k).run u base=VirtualLeaf.config k ((IngressRepair.machine k).run u old) :=
    (ct u hu).trans (vt u hu)
  have safe (u : Nat) (hu : u<t) :
      ((CanonicalLeaf.machine k).run u base).state ≠ cut k 430 ∧
      ((CanonicalLeaf.machine k).run u base).state ≠ cut k 613 := by
    rw [eq u (by omega)]
    have bound:=prior u hu
    change ((IngressRepair.machine k).run u old).state.val < 139 at bound
    constructor
    all_goals intro bad; have e:=congrArg Fin.val bad
    all_goals rw [cut_val k _ (by unfold Cursor.stateCount; omega)] at e
    all_goals change ((IngressRepair.machine k).run u old).state.val=288+_+93*k at e
    all_goals omega
  have tx:=transport base safe t le_rfl
  refine ⟨t,ht,?_,negative⟩
  have last:=congrArg Config.state (tx.trans (congrArg (config k) (eq t le_rfl)))
  change _=embed k (VirtualLeaf.embed k ((IngressRepair.machine k).run t old).state) at last
  rw [done] at last
  exact last
end CarryWindow
