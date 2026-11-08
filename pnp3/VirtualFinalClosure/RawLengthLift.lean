import VirtualFinalClosure.RawLength
import TotalIngressClosure.SupportedLift
namespace VirtualFinalClosure.RawLengthLift
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion PairEncoding Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("TotalIngressClosure.SupportedLift","TotalIngressClosure","lift_supported_prefix","bodyPrefix"),
      ("VirtualLeaf.Transport","VirtualLeaf","entry_val","entryValue"),
      ("VirtualFinalClosure.RawLength","VirtualFinalClosure.RawLength","raw_length","rawLength")] do
    let found:=env.constants.toList.filter fun (n,_)=>n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,.thmInfo ci)]=>
      logInfo m!"private-term|{n}|kind=theorem|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique real early raw family transport {mod}/{key}"
private theorem virtual_state (k : Nat) {N B : Nat} (c : Config (IngressRepair.machine k).stateCount N B) :
    (VirtualLeaf.config k c).state.val=c.state.val := by dsimp only [VirtualLeaf.config,VirtualLeaf.embed]
private theorem carry_state (k : Nat) {N B : Nat} (c : Config (CanonicalLeaf.machine k).stateCount N B) :
    (CarryWindow.config k c).state.val=c.state.val := by dsimp only [CarryWindow.config,CarryWindow.embed]
private theorem body_state (k : Nat) {N B : Nat} (c : Config (CarryWindow.machine k).stateCount N B) :
    (BodyIngress.config k c).state.val=c.state.val := by dsimp only [BodyIngress.config,BodyIngress.old]
private theorem embed_state (k : Nat) {N B : Nat} (c : Config (AllArityCursor.machine k).stateCount N B) :
    (BodyIngress.config k (CarryWindow.config k (VirtualLeaf.config k c))).state.val=c.state.val := by
  rw [body_state,carry_state,virtual_state]
/-- This changes no execution control or tape: it applies the reviewed repair
and exact guarded component embeddings to every edge of an actual early run. -/
private theorem early_body (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (z : Nat) (tag : FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (physical : z=0 ∨ 9+z<a+m) (t : Nat)
    (prior : ∀ u,u<t → ((AllArityCursor.machine k).run u
      (initialConfig (AllArityCursor.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state.val ≤ 617) :
    ∀ u,u≤t → (BodyIngress.machine k).run u
      (initialConfig (BodyIngress.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))=
      BodyIngress.config k (CarryWindow.config k (VirtualLeaf.config k ((AllArityCursor.machine k).run u
        (initialConfig (AllArityCursor.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))))) := by
  apply bodyPrefix k x w z tag gamma physical t
  · intro u hu eq
    have same:=congrArg Fin.val eq
    rw [entryValue] at same
    exact (Nat.ne_of_lt (lt_of_le_of_lt (prior u hu) (by omega))) same
  · intro u hu j hj eq
    have same:=congrArg Fin.val eq
    change ((AllArityCursor.machine k).run u
      (initialConfig (AllArityCursor.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state.val=
        288+(j+93*k)%Cursor.stateCount k at same
    have bound : j+93*k < Cursor.stateCount k := by rcases hj with rfl|rfl <;> unfold Cursor.stateCount <;> omega
    rw [Nat.mod_eq_of_lt bound] at same
    have high : 617 < 288+(j+93*k) := by rcases hj with rfl|rfl <;> omega
    exact (Nat.ne_of_lt (lt_of_le_of_lt (prior u hu) high)) same
/-- Supported all-arity original RAW start, not a prepared q201 installation.
The exact dependent image and strict three-state avoidance are retained. -/
private theorem raw_length_body (k : Nat) {a m n consumed z : Nat} (x : Bitstring a) (w : Bitstring m)
    (header : contentHeader? (Fin.append x w)=some (n,consumed))
    (tag : FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (firstPhysical : z=0 ∨ 9+z<a+m) (cap : n<FixedRawLengthFence.capacity a m z)
    (rows : 2^n ≤ FixedRawLengthFence.fencePos (pairLength a m)-(a+m+z+n+3)-1)
    (physical : min (9+2*z+2^n) (a+m)<a+m) :
    let S:=a+m;let R:=pairLength a m;let B:=FixedRawLengthFence.allocation R
    let L:=S+z+2;let F:=3*R+2;let r:=S-min (9+2*z+2^n) S
    let U:=Body.extend (Body.installedTape (SmallIngress.prepared B x w z n) L n)
    let V:=Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
    let X:=CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r
    let Y:=RuntimeBitLength.Target.fullImage X L n F r
    let c:=initialConfig (BodyIngress.machine k) B (encodePair x w)
    let old:=initialConfig (AllArityCursor.machine k) B (encodePair x w)
    ∃ (t : Nat) (h : (if bitLength n≤r then L else F+r+n+3)<tapeLength R B),
      t≤4194304*(R+1)^3 ∧
      (BodyIngress.machine k).run t c=BodyIngress.config k (CarryWindow.config k (VirtualLeaf.config k
        (SmallIngress.producer.seqEmbedRight (Cursor.machine k)
          ⟨Cursor.q k (if bitLength n≤r then 308 else if (r+1)%2=1 then 250 else 304),
            ⟨if bitLength n≤r then L else F+r+n+3,h⟩,fun i=>Y i.val⟩))) ∧
      (∀ u,u≤t → (BodyIngress.machine k).run u c=BodyIngress.config k
        (CarryWindow.config k (VirtualLeaf.config k ((AllArityCursor.machine k).run u old)))) ∧
      (∀ u,u≤t → ((BodyIngress.machine k).run u c).head.val≤12*(R+1)^2) ∧
      (∀ u,u<t → ((AllArityCursor.machine k).run u old).state≠SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k 250) ∧
        ((AllArityCursor.machine k).run u old).state≠SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k 304) ∧
        ((AllArityCursor.machine k).run u old).state≠SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k 308) ∧
        ((AllArityCursor.machine k).run u old).state≠SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k (798+93*k))) ∧
      (∀ u,u≤t → ((BodyIngress.machine k).run u c).state.val≤617) := by
  intro S R B L F r U V X Y c old
  obtain ⟨t,h,price,done,heads,avoid,before⟩:=rawLength k x w header tag gamma firstPhysical cap rows physical
  have lifted:=early_body k x w z tag gamma firstPhysical t (fun u hu=>before u hu.le)
  refine ⟨t,h,price,?_,lifted,?_,avoid,?_⟩
  · rw [lifted t le_rfl,done]
  · intro u hu
    rw [lifted u hu]
    exact heads u hu
  · intro u hu
    rw [lifted u hu,embed_state]
    exact before u hu
#print axioms early_body
#print axioms raw_length_body
end VirtualFinalClosure.RawLengthLift
