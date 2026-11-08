import TotalIngressClosure.WideProducer
namespace TotalIngressClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion PairEncoding Lean Elab Command
attribute [local irreducible] UniformTM.run
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("VirtualLeaf.Transport","VirtualLeaf","transport","virtualTransport"),
      ("VirtualLeaf.Transport","VirtualLeaf","inject","virtualInject"),
      ("CanonicalLeaf.Rows","CanonicalLeaf","transport","canonicalTransport"),
      ("CarryWindow.Transport","CarryWindow","transport","carryTransport")] do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,.thmInfo ci)] =>
      logInfo m!"private-term|{n}|kind=theorem|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _=>throwError "Nonunique guarded literal transport {mod}/{key}: {found.map Prod.fst}"
private def guardedEmbed {k N B : Nat} (c : Config (IngressRepair.machine k).stateCount N B) :
    Config (BodyIngress.machine k).stateCount N B:=
  BodyIngress.config k (CarryWindow.config k (VirtualLeaf.config k c))
set_option maxRecDepth 4000 in
private theorem lift_supported_prefix (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (z : Nat) (tag:FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (gamma:FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (physical:z=0 ∨ 9+z < a+m) (t : Nat)
    (ready : ∀ u,u < t → ((AllArityCursor.machine k).run u
      (initialConfig (AllArityCursor.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state ≠
        VirtualLeaf.entry k)
    (cut : ∀ u,u < t → ∀ j,j=430 ∨ j=613 → ((AllArityCursor.machine k).run u
      (initialConfig (AllArityCursor.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state ≠
        IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.q k (j+93*k))) :
    ∀ u,u ≤ t → (BodyIngress.machine k).run u
      (initialConfig (BodyIngress.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))=
      guardedEmbed (k:=k) ((AllArityCursor.machine k).run u
        (initialConfig (AllArityCursor.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))) := by
  let B:=FixedRawLengthFence.allocation (pairLength a m)
  let repaired:=initialConfig (IngressRepair.machine k) B (encodePair x w)
  let virtual:=VirtualLeaf.config k repaired
  let carry:=CarryWindow.config k virtual
  have repair (u : Nat) : (IngressRepair.machine k).run u repaired=(AllArityCursor.machine k).run u
      (initialConfig (AllArityCursor.machine k) B (encodePair x w)):=IngressRepair.supported_transport k x w z tag gamma physical u
  have vt:=virtualTransport repaired (t:=t) (by intro u hu;rw [repair];exact ready u hu)
  have ct:=canonicalTransport virtual (t:=t) (by
    intro u hu
    rw [vt u (Nat.le_of_lt hu)]
    exact ((IngressRepair.machine k).run u repaired).state.isLt)
  have before (u : Nat) (hu : u ≤ t) : (CanonicalLeaf.machine k).run u virtual=
      VirtualLeaf.config k ((AllArityCursor.machine k).run u
        (initialConfig (AllArityCursor.machine k) B (encodePair x w))):=by
    rw [ct u hu,vt u hu,repair u]
  have kt:=carryTransport virtual (t:=t) (by
    intro u hu
    rw [before u (Nat.le_of_lt hu)]
    constructor
    · intro bad
      apply cut u hu 430 (Or.inl rfl)
      exact virtualInject k bad
    · intro bad
      apply cut u hu 613 (Or.inr rfl)
      exact virtualInject k bad)
  have bt:=BodyIngress.transport carry (t:=t) (by
    intro u hu bad
    rw [kt u (Nat.le_of_lt hu),before u (Nat.le_of_lt hu)] at bad
    have eq:=congrArg Fin.val bad
    change _=(CanonicalLeaf.machine k).stateCount+24 at eq
    have small:=((AllArityCursor.machine k).run u
      (initialConfig (AllArityCursor.machine k) B (encodePair x w))).state.isLt
    change ((AllArityCursor.machine k).run u
      (initialConfig (AllArityCursor.machine k) B (encodePair x w))).state.val=(CanonicalLeaf.machine k).stateCount+24 at eq
    change _ < (IngressRepair.machine k).stateCount at small
    have larger : (IngressRepair.machine k).stateCount ≤ (CanonicalLeaf.machine k).stateCount:=by
      change (IngressRepair.machine k).stateCount ≤ (IngressRepair.machine k).stateCount+8
      omega
    omega)
  intro u hu
  have initial : BodyIngress.config k carry=initialConfig (BodyIngress.machine k) B (encodePair x w):=rfl
  rw [← initial,bt u hu,kt u hu,ct u hu,vt u hu,repair u]
  rfl
end TotalIngressClosure
