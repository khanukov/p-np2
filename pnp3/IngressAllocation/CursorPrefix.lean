import IngressAllocation.RawStream
import IngressAllocation.EarlyLift
import IngressAllocation.Endpoint
namespace IngressAllocation
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command
attribute [local irreducible] UniformTM.run
run_cmd do
  let env ← getEnv
  for (mod,key,aliasName) in [("RawStream","raw_stream_heads","streamHeads"),
      ("EarlyLift","lift_early_prefix","liftEarly"),("Geometry","old_le_new","budgetMono"),
      ("Endpoint","reallocate_prefix","reallocatePrefix")] do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith ("_private.IngressAllocation."++mod++".") && n.toString.endsWith (".IngressAllocation."++key)
    match found with
    | [(n,.thmInfo ci)] =>
      logInfo m!"private-term|{n}|kind=theorem|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _=>throwError "Nonunique actual raw cursor interface {mod}/{key}: {found.map Prod.fst}"
set_option maxRecDepth 4000 in
private theorem cursor_prefix_heads (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (accepted : PartAEndpoint.thresholdContentWitnessRelation k a m x w=true)
    {pr : AcceptedBody.Parsed k}
    (parsed : contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr) :
    ∃ (z t : Nat) (_hH : a+m+z+pr.2.n+3 < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m))),
      FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z ∧ t ≤ 4096*((pairLength a m)+1)^2 ∧
      let U:=Body.extend (Body.installedTape (SmallIngress.prepared (FixedRawLengthFence.allocation (pairLength a m)) x w z pr.2.n) (a+m+z+2) pr.2.n)
      let V:=Stream.Target.image U (a+m) z pr.2.n (9+2*z) (2^pr.2.n) (2^pr.2.n) false
      let p:=min (9+2*z+2^pr.2.n) (a+m)
      let c:=initialConfig (AllArityCursor.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)
      ∃ hp : p < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m)),
        (AllArityCursor.machine k).run t c=SmallIngress.producer.seqEmbedRight (Cursor.machine k)
          ⟨Cursor.q k (if p=a+m then 57 else 58),⟨p,hp⟩,fun i=>V i.val⟩ ∧
        (∀ u,u < t → ((AllArityCursor.machine k).run u c).state.val ≠ 345 ∧
          ((AllArityCursor.machine k).run u c).state.val ≠ 346) ∧
        (∀ u,u ≤ t → ((AllArityCursor.machine k).run u c).state.val < 352) ∧
        Footprint (AllArityCursor.machine k) (C:=(FixedRawLengthFence.allocation (pairLength a m))) (encodePair x w) t (12*((pairLength a m)+1)^2) := by
  let R:=pairLength a m
  let B:=FixedRawLengthFence.allocation R
  obtain ⟨pr0,parse0,_table,z,T,t,hH,gamma,price,timeLe,_twoPrice,hp,_hp1,_oldAtT,oldAtFirst,tx,first,
    _paid,done,_eof,_physical⟩:=AllArityCursor.accepted_raw k x w accepted
  have same : pr0=pr:=Option.some.inj (parse0.symm.trans parsed)
  cases same
  obtain ⟨otherZ,otherT,_otherH,otherGamma,_otherPrice,otherP,otherRun,otherHeads⟩:=streamHeads k x w accepted parsed
  have sameZ : otherZ=z:=Option.some.inj (otherGamma.symm.trans gamma)
  cases sameZ
  have beforeBound : t ≤ otherT := by
    by_contra later
    have absent:=first otherT (by omega)
    rw [otherRun] at absent
    by_cases atEnd : Stream.Target.cursor (9+2*z) (a+m) (2^pr.2.n)=a+m
    · simp only [if_pos atEnd] at absent
      exact absent.1 rfl
    · simp only [if_neg atEnd] at absent
      exact absent.2.1 rfl
  refine ⟨z,t,hH,gamma,timeLe.trans price,hp,done,?_,?_,?_⟩
  · intro u hu
    exact ⟨(first u hu).2.2.1,(first u hu).2.2.2⟩
  · intro u hu
    rw [tx u hu]
    exact (SmallIngress.machine.run u
      (initialConfig SmallIngress.machine (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state.isLt
  · intro u hu
    rw [tx u hu]
    exact otherHeads u (hu.trans beforeBound)
end IngressAllocation
