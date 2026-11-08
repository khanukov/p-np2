import IngressAllocation.RepairHeader
import IngressAllocation.RepairPrefix
import IngressAllocation.RepairTarget
import IngressAllocation.Endpoint
namespace IngressAllocation
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command
attribute [local irreducible] UniformTM.run
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("IngressAllocation.RepairHeader","IngressAllocation","header_positive","headerPositive"),
      ("IngressAllocation.RepairHeader","IngressAllocation","missing_time_bound","timeBound"),
      ("IngressAllocation.RepairPrefix","IngressAllocation","repair_low_prefix","repairPrefix"),
      ("IngressAllocation.RepairPrefix","IngressAllocation","repairEmbed","repairEmbed"),
      ("IngressAllocation.Endpoint","IngressAllocation","reallocate_prefix","reallocatePrefix"),
      ("IngressAllocation.Geometry","IngressAllocation","old_le_new","budgetMono"),
      ("IngressRepair.Header","IngressRepair","put","headerPut"),
      ("IngressRepair.Header","IngressRepair","source","headerSource"),
      ("IngressRepair.Transport","IngressRepair","raw_at_low","rawLow"),
      ("IngressRepair.Transport","IngressRepair","producer_path","producerPath"),
      ("IngressRepair.Transport","IngressRepair","prefix_equal","prefixEqual"),
      ("IngressRepair.Transport","IngressRepair","safe_low","safeLow"),
      ("IngressRepair.Transport","IngressRepair","guard_step","guardStep"),
      ("IngressRepair.Transport","IngressRepair","before_low","beforeLow")] do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)] =>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _=>throwError "Nonunique sharp repaired reject composition {mod}/{key}: {found.map Prod.fst}"
set_option maxRecDepth 4000 in
private theorem sharp_reject (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m) (z : Nat)
    (tag : FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (positive : 0 < z) (short : a+m=9+z) :
    ∃ (t : Nat) (hS : a+m < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m))),
      t ≤ 12*(pairLength a m+1)^2 ∧
      (BodyIngress.machine k).run t
        (initialConfig (BodyIngress.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))=
        ⟨(BodyIngress.machine k).reject,⟨a+m,hS⟩,
          Function.update (Function.update (FixedRawLengthFence.fencedContentTape (FixedRawLengthFence.allocation (pairLength a m)) x w)
            ⟨7,by omega⟩ none) ⟨8,by omega⟩ none⟩:=by
  let R:=pairLength a m;let B:=FixedRawLengthFence.allocation R
  let g:=FixedRawLengthFence.installClock R+FixedRawLengthFence.contentClock a m+3*(a+m)+7
  let T:=g+(5*z+9)
  let c:=initialConfig (IngressRepair.machine k) B (encodePair x w)
  obtain ⟨h,arrived⟩:=headerPositive x w z tag gamma positive
  change 9+z < tapeLength R B at h
  change SmallIngress.producer.run T (initialConfig SmallIngress.producer B (encodePair x w))=_ at arrived
  have full : SmallIngress.producer.run T (initialConfig SmallIngress.producer B (encodePair x w))=
      ⟨SmallIngress.q 138,⟨9+z,h⟩,
        Function.update (Function.update (FixedRawLengthFence.fencedContentTape B x w)
          ⟨7,by change 7 < tapeLength R B;omega⟩ none) ⟨8,by change 8 < tapeLength R B;omega⟩ none⟩:=by
    rw [arrived]
    apply Config.ext_parts
    · rfl
    · rfl
    · funext i
      simp only [headerPut,Function.update_apply,Fin.ext_iff]
      rfl
  have low:=rawLow k x w T 138 (by decide) (by rw [full];rfl)
  have whole:=producerPath k x w T (by rw [full];change SmallIngress.q 138 ≠ SmallIngress.producer.accept;decide)
  change ((AllArityCursor.machine k).run T c).state.val=138 at low
  change (AllArityCursor.machine k).run T c=_ at whole
  have same (u : Nat) (hu : u ≤ T) : (IngressRepair.machine k).run u c=(AllArityCursor.machine k).run u c:=
    prefixEqual k c u (fun v hv=>safeLow k c T (by rw [low];decide) v (by omega))
  have blank : ((AllArityCursor.machine k).run T c).tape ((AllArityCursor.machine k).run T c).head=none:=by
    rw [whole,full]
    have nf : 9+z ≠ FixedRawLengthFence.fencePos (pairLength a m):=by
      dsimp only [FixedRawLengthFence.fencePos,pairLength];omega
    simp [UniformTM.seqEmbedRouted,Function.update_apply,Fin.ext_iff,FixedRawLengthFence.fencedContentTape,short,nf]
  have finalStep:=guardStep k ((AllArityCursor.machine k).run T c) low blank
  have prior (u : Nat) (hu : u < T+1) : ((IngressRepair.machine k).run u c).state.val < 139:=by
    rw [same u (by omega)]
    exact beforeLow k c T (by rw [low];decide) u (by omega)
  have repaired : (IngressRepair.machine k).run (T+1) c=
      ⟨(IngressRepair.machine k).reject,⟨9+z,h⟩,
        Function.update (Function.update (FixedRawLengthFence.fencedContentTape B x w)
          ⟨7,by change 7 < tapeLength R B;omega⟩ none) ⟨8,by change 8 < tapeLength R B;omega⟩ none⟩:=by
    rw [UniformTM.run,same T le_rfl,finalStep,whole,full]
    rfl
  have tx:=repairPrefix c prior
  have cost:=timeBound a m z short
  change g+5*z+10 ≤ 12*(R+1)^2 at cost
  have price : T+1 ≤ 12*(R+1)^2:=by dsimp only [T];omega
  refine ⟨T+1,by simpa only [short] using h,price,?_⟩
  have enter : repairEmbed c=initialConfig (BodyIngress.machine k) B (encodePair x w):=rfl
  rw [← enter,tx (T+1) le_rfl,repaired]
  apply Config.ext_parts
  · rfl
  · apply Fin.ext
    exact short.symm
  · rfl
set_option maxRecDepth 4000 in
theorem missing_payload (k : Nat) : Target.MissingPayload k:=by
  intro a m x w z tag gamma positive short
  obtain ⟨t,hS,price,done⟩:=sharp_reject k x w z tag gamma positive short
  let R:=pairLength a m;let B:=FixedRawLengthFence.allocation R
  let c:=initialConfig (BodyIngress.machine k) B (encodePair x w)
  let large:=initialConfig (BodyIngress.machine k) (allocation k R) (encodePair x w)
  have heads : Footprint (BodyIngress.machine k) (C:=B) (encodePair x w) t (12*(R+1)^2):=by
    intro u hu
    exact ((BodyIngress.machine k).run_initialConfig_head_le (budget:=B) (steps:=u) (encodePair x w)).trans (hu.trans price)
  obtain ⟨room,trace,extended⟩:=reallocatePrefix k R t (encodePair x w) heads
  have rejected : ((BodyIngress.machine k).run t large).state=(BodyIngress.machine k).reject:=by
    rw [extended,done]
    rfl
  obtain ⟨_time,_budget,_oldReject,negative⟩:=BodyIngress.missing_payload k x w z tag gamma positive short
  refine ⟨budgetMono k R,FixedPairParser.initialConfig_extension (BodyIngress.machine k) (budgetMono k R) (encodePair x w),
    t,hS,price,done,heads,room,trace,extended,rejected,?_,negative⟩
  intro u hu bad
  have later:=(BodyIngress.machine k).run_accept_of_le large bad hu
  rw [later,bad] at rejected
  exact (BodyIngress.machine k).accept_ne_reject rejected
end IngressAllocation
