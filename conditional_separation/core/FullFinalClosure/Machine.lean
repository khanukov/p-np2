import VirtualFinalClosure.Finite
import NormalFinalClosure.Machine2
namespace FullFinalClosure
open Pnp3.Complexity.Uniform.V1
set_option autoImplicit false
set_option maxRecDepth 512
set_option maxHeartbeats 200000
/-- Disjoint finite state space. Only k is executable constructor data. -/
def count (k : Nat) : Nat := (VirtualFinalClosure.machine k).stateCount+(NormalFinalClosure.machine2 k).stateCount
def left (k : Nat) (q : Fin (VirtualFinalClosure.machine k).stateCount) : Fin (count k) :=
  ⟨q.val,by have h:=q.isLt;unfold count;omega⟩
/-- Shared literal terminals; every other consumer control has a disjoint offset. -/
def right (k : Nat) (q : Fin (NormalFinalClosure.machine2 k).stateCount) : Fin (count k) :=
  if q=(NormalFinalClosure.machine2 k).accept then left k (VirtualFinalClosure.machine k).accept
  else if q=(NormalFinalClosure.machine2 k).reject then left k (VirtualFinalClosure.machine k).reject
  else ⟨(VirtualFinalClosure.machine k).stateCount+q.val,by have h:=q.isLt;unfold count;omega⟩
def entryA (k : Nat) (mode : Fin 3) : Fin (VirtualFinalClosure.machine k).stateCount :=
  VirtualFinalClosure.control k (CertificateGuardClosure.old k (TotalIngressClosure.old k
    (BodyIngress.body k (SerializedBody.entry mode)))) ⟨8,by decide⟩
def entryB (k : Nat) (mode : Fin 3) : Fin (NormalFinalClosure.machine2 k).stateCount :=
  NormalFinalClosure.old2 k (RawCallerClosure.callerState k (PhysicalCallerClosure.oldState k
    (BodyIngress.body k (SerializedBody.entry mode))))
/-- Exactly three changed A controls, all at normalized metadata 8. -/
def dispatch (k : Nat) (q : Fin (VirtualFinalClosure.machine k).stateCount) : Option (Fin 3) :=
  if q=entryA k 0 then some 0 else if q=entryA k 1 then some 1
  else if q=entryA k 2 then some 2 else none
def rows (k : Nat) (s : Fin (count k)) (b : Option Bool) : Fin (count k) × Option Bool × Move :=
  if h:s.val < (VirtualFinalClosure.machine k).stateCount then
    let q : Fin (VirtualFinalClosure.machine k).stateCount:=⟨s.val,h⟩
    match dispatch k q with
    | some mode=>(right k (entryB k mode),b,.stay)
    | none=>let a:=(VirtualFinalClosure.machine k).step q b;(left k a.1,a.2)
  else
    let q : Fin (NormalFinalClosure.machine2 k).stateCount:=
      ⟨s.val-(VirtualFinalClosure.machine k).stateCount,by have h:=s.isLt;unfold count at h;omega⟩
    let a:=(NormalFinalClosure.machine2 k).step q b
    (right k a.1,a.2)
/-- Complete executable raw-to-FINAL candidate, fixed once per k. -/
def machine (k : Nat) : UniformTM where
  stateCount:=count k
  start:=left k (VirtualFinalClosure.machine k).start
  accept:=left k (VirtualFinalClosure.machine k).accept
  reject:=left k (VirtualFinalClosure.machine k).reject
  accept_ne_reject:=by
    intro h
    apply (VirtualFinalClosure.machine k).accept_ne_reject
    have hv:=congrArg (fun q:Fin (count k)=>q.val) h
    change (VirtualFinalClosure.machine k).accept.val=(VirtualFinalClosure.machine k).reject.val at hv
    exact Fin.ext hv
  rawStep:=rows k
def configA (k : Nat) {N B : Nat} (c : Config (VirtualFinalClosure.machine k).stateCount N B) :
    Config (machine k).stateCount N B := ⟨left k c.state,c.head,c.tape⟩
def configB (k : Nat) {N B : Nat} (c : Config (NormalFinalClosure.machine2 k).stateCount N B) :
    Config (machine k).stateCount N B := ⟨right k c.state,c.head,c.tape⟩
/-- Explicit coarse total price, including the real handoff stay. -/
def runtimeBound (k N : Nat) : Nat := VirtualFinalClosure.deadline k N+17592186044416*(k+1)*(N+1)^8+1
/-- Extra time is allocated as real tape; never a live absorbing timeout. -/
def allocation (k N : Nat) : Nat := VirtualFinalClosure.allocation k N+runtimeBound k N+1
/-- Fixed computable degree large enough for N=0 and N=1 as well as N≥2. -/
def degree (k : Nat) : Nat := 2^(4*k+128)*(k+1)^8+4*k+128
end FullFinalClosure
