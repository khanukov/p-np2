import TotalIngressClosure.SupportedLift
namespace TotalIngressClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command
attribute [local irreducible] UniformTM.run
run_cmd do
  let env ← getEnv
  let specs:=( ["After","CQ","below_cuts","after_run","after_ne"].map fun key=>
    ("CarryReadyCompletion.Virtual","CarryReadyCompletion",key,key)) ++
    [("VirtualLeaf.Transport","VirtualLeaf","entry_val","entryValue"),
     ("VirtualLeaf.Transport","VirtualLeaf","transport","virtualTransport"),
     ("CanonicalLeaf.Rows","CanonicalLeaf","transport","canonicalTransport")]
  for (mod,ns,key,aliasName) in specs do
    let found:=env.constants.toList.filter fun (n,_)=>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)]=>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique literal virtual control trap {mod}/{key}: {found.map Prod.fst}"
set_option maxRecDepth 4000 in
private theorem canonical_prefix (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (z : Nat) (tag:FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (gamma:FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (physical:z=0 ∨ 9+z < a+m) (t : Nat)
    (prior : ∀ u, u     <     t      →      ((AllArityCursor.machine k).run u
      (initialConfig (AllArityCursor.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state.val     <     288+430+93*k) :
    let old:=initialConfig (IngressRepair.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)
    let c:=initialConfig (CanonicalLeaf.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)
    ∀ u, u     ≤     t      →      (CanonicalLeaf.machine k).run u c=VirtualLeaf.config k ((IngressRepair.machine k).run u old) := by
  intro old c
  have low (u : Nat) (hu : u     <     t) : ((IngressRepair.machine k).run u old).state.val     <     288+430+93*k := by
    rw [IngressRepair.supported_transport k x w z tag gamma physical u]; exact prior u hu
  have entryval:=entryValue k
  have a:=virtualTransport old (t:=t) (by
      intro u hu bad
      have b:=low u hu
      rw [bad,entryval] at b; omega)
  have b:=canonicalTransport (VirtualLeaf.config k old) (t:=t) (by
      intro u hu; rw [a u (by omega)]
      have bound:=low u hu
      change ((IngressRepair.machine k).run u old).state.val     <     (IngressRepair.machine k).stateCount
      change _     <     288+Cursor.stateCount k
      unfold Cursor.stateCount; omega)
  intro u hu; exact (b u hu).trans (a u hu)
set_option maxRecDepth 4000 in
private theorem never_cuts (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (z : Nat) (tag:FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (gamma:FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (physical:z=0 ∨ 9+z < a+m) (t : Nat)
    (prior : ∀ u, u     <     t      →      ((AllArityCursor.machine k).run u
      (initialConfig (AllArityCursor.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state.val     <     288+430+93*k)
    (event : After k (VirtualLeaf.embed k (((AllArityCursor.machine k).run t
      (initialConfig (AllArityCursor.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state))) :
    let c:=initialConfig (CanonicalLeaf.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)
    ∀ u, ((CanonicalLeaf.machine k).run u c).state     ≠     CQ k (430+93*k)      ∧
      ((CanonicalLeaf.machine k).run u c).state     ≠     CQ k (613+93*k) := by
  intro c
  have prefixEq:=canonical_prefix k x w z tag gamma physical t prior
  have eq (u : Nat) (hu : u   ≤   t) : (CanonicalLeaf.machine k).run u c=
      VirtualLeaf.config k ((AllArityCursor.machine k).run u
        (initialConfig (AllArityCursor.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))) := by
    have h:=prefixEq u hu
    rw [IngressRepair.supported_transport k x w z tag gamma physical] at h
    exact h
  have atEvent : After k ((CanonicalLeaf.machine k).run t c).state := by
    rw [eq t le_rfl]; exact event
  intro u
  by_cases early : u     <     t
  · apply below_cuts k
    rw [eq u (by omega)]
    exact prior u early
  · have later:=after_run ((CanonicalLeaf.machine k).run t c) atEvent (u-t)
    rw [←UniformTM.run_add,show t+(u-t)=u by omega] at later
    exact after_ne later

end TotalIngressClosure
