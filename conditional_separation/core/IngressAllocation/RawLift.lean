import IngressAllocation.Endpoint
namespace IngressAllocation
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command
attribute [local irreducible] UniformTM.run
run_cmd do
  let env ← getEnv
  for (mod,key,aliasName) in [("Geometry","old_le_new","budgetMono"),("Endpoint","reallocate_prefix","reallocatePrefix")] do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith ("_private.IngressAllocation."++mod++".") && n.toString.endsWith (".IngressAllocation."++key)
    match found with
    | [(n,.thmInfo ci)] =>
      logInfo m!"private-term|{n}|kind=theorem|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _=>throwError "Nonunique whole-prefix extension theorem {mod}/{key}: {found.map Prod.fst}"
set_option maxRecDepth 4000 in
private theorem raw_of_footprints (k : Nat)
    (leafHeads : ∀ {a m : Nat} (x : Bitstring a) (w : Bitstring m),
      PartAEndpoint.thresholdContentWitnessRelation k a m x w=true →
      ∀ t,((BodyIngress.machine k).run t
        (initialConfig (BodyIngress.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state=
        BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k false)) →
      (∀ u,u < t → ∀ b,((BodyIngress.machine k).run u
        (initialConfig (BodyIngress.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state ≠
          BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k b))) →
      Footprint (BodyIngress.machine k) (C:=FixedRawLengthFence.allocation (pairLength a m))
        (encodePair x w) t (12*(pairLength a m+1)^2))
    (bodyHeads : ∀ {a m : Nat} (x : Bitstring a) (w : Bitstring m),
      PartAEndpoint.thresholdContentWitnessRelation k a m x w=true →
      ∀ t mode,((BodyIngress.machine k).run t
        (initialConfig (BodyIngress.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state=
        BodyIngress.body k (SerializedBody.entry mode) →
      (∀ u,u < t → ∀ selected:Fin 3,((BodyIngress.machine k).run u
        (initialConfig (BodyIngress.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state ≠
          BodyIngress.body k (SerializedBody.entry selected)) →
      Footprint (BodyIngress.machine k) (C:=FixedRawLengthFence.allocation (pairLength a m))
        (encodePair x w) t (12*(pairLength a m+1)^2)) : Target.Raw k := by
  intro a m x w accepted
  obtain ⟨pr,parsed,z,hH,gamma,eof,physical⟩:=FullIngressClosure.raw k x w accepted
  refine ⟨pr,parsed,z,hH,gamma,budgetMono k (pairLength a m),
    FixedPairParser.initialConfig_extension (BodyIngress.machine k) (budgetMono k (pairLength a m)) (encodePair x w),?_,?_⟩
  · intro equal
    obtain ⟨positive,logical,zeros,decoded,t,s,st,price,oldEnd,oldFirst,firstOld,atEntry,localPrice,done,safe,first⟩:=eof equal
    have atResult : ((BodyIngress.machine k).run (s+5)
        (initialConfig (BodyIngress.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state=
        BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k false)) := by rw [done]
    have heads:=leafHeads x w accepted (s+5) atResult first
    obtain ⟨room,trace,extended⟩:=reallocatePrefix k (pairLength a m) (s+5) (encodePair x w) heads
    refine ⟨positive,logical,zeros,decoded,t,s,st,price,oldEnd,oldFirst,firstOld,atEntry,localPrice,done,safe,first,
      heads,room,trace,extended.trans (congrArg (fun c : Config (BodyIngress.machine k).stateCount (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m)) => extendConfig (budgetMono k (pairLength a m)) c) done),?_,?_⟩
    · intro u hu b
      rw [← (trace u (Nat.le_of_lt hu)).1]
      exact first u hu b
    · intro u hu
      rw [← (trace u hu).1]
      exact safe u hu
  · intro phys
    obtain ⟨fit,branch⟩:=physical phys
    refine ⟨fit,?_⟩
    rcases branch with ⟨overflow,logical,leaf⟩ | ⟨ellFits,branch⟩
    · refine Or.inl ⟨overflow,logical,?_⟩
      obtain ⟨positive,logical,zeros,decoded,t,s,st,price,oldEnd,oldFirst,firstOld,atEntry,localPrice,done,safe,first⟩:=leaf
      have atResult : ((BodyIngress.machine k).run (s+5)
          (initialConfig (BodyIngress.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state=
          BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k false)) := by rw [done]
      have heads:=leafHeads x w accepted (s+5) atResult first
      obtain ⟨room,trace,extended⟩:=reallocatePrefix k (pairLength a m) (s+5) (encodePair x w) heads
      refine ⟨positive,logical,zeros,decoded,t,s,st,price,oldEnd,oldFirst,firstOld,atEntry,localPrice,done,safe,first,
        heads,room,trace,extended.trans (congrArg (fun c : Config (BodyIngress.machine k).stateCount (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m)) => extendConfig (budgetMono k (pairLength a m)) c) done),?_,?_⟩
      · intro u hu b
        rw [← (trace u (Nat.le_of_lt hu)).1]
        exact first u hu b
      · intro u hu
        rw [← (trace u hu).1]
        exact safe u hu
    · refine Or.inr ⟨ellFits,?_⟩
      rcases branch with normal | ⟨v2,v3,v4,v5,d,cap,logical,leaf⟩
      · obtain ⟨wFits,t,d,e,ht,hd,td,atW,firstW,atReady,firstReady,fit12,he,total,source,done,first,safe⟩:=normal
        let mode:=SerializedBody.sourceMode (Fin.append x w) (Cursor.Target.M k pr.2.n z)
        have atEntry : ((BodyIngress.machine k).run (t+d+e)
            (initialConfig (BodyIngress.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state=
            BodyIngress.body k (SerializedBody.entry mode) := by rw [done]
        have heads:=bodyHeads x w accepted (t+d+e) mode atEntry first
        obtain ⟨room,trace,extended⟩:=reallocatePrefix k (pairLength a m) (t+d+e) (encodePair x w) heads
        refine Or.inl ⟨wFits,t,d,e,ht,hd,td,atW,firstW,atReady,firstReady,fit12,he,total,source,done,first,safe,
          heads,room,trace,extended.trans (congrArg (fun c : Config (BodyIngress.machine k).stateCount (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m)) => extendConfig (budgetMono k (pairLength a m)) c) done),?_,?_⟩
        · intro u hu mode
          rw [← (trace u (Nat.le_of_lt hu)).1]
          exact first u hu mode
        · intro u hu
          rw [← (trace u hu).1]
          exact safe u hu
      · refine Or.inr ⟨v2,v3,v4,v5,d,cap,logical,?_⟩
        obtain ⟨positive,logical,zeros,decoded,t,s,st,price,oldEnd,oldFirst,firstOld,atEntry,localPrice,done,safe,first⟩:=leaf
        have atResult : ((BodyIngress.machine k).run (s+5)
            (initialConfig (BodyIngress.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state=
            BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k false)) := by rw [done]
        have heads:=leafHeads x w accepted (s+5) atResult first
        obtain ⟨room,trace,extended⟩:=reallocatePrefix k (pairLength a m) (s+5) (encodePair x w) heads
        refine ⟨positive,logical,zeros,decoded,t,s,st,price,oldEnd,oldFirst,firstOld,atEntry,localPrice,done,safe,first,
          heads,room,trace,extended.trans (congrArg (fun c : Config (BodyIngress.machine k).stateCount (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m)) => extendConfig (budgetMono k (pairLength a m)) c) done),?_,?_⟩
        · intro u hu b
          rw [← (trace u (Nat.le_of_lt hu)).1]
          exact first u hu b
        · intro u hu
          rw [← (trace u hu).1]
          exact safe u hu
end IngressAllocation
