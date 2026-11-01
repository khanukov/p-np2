import TotalIngressClosure.Machine
namespace TotalIngressClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command
attribute [local irreducible] UniformTM.run
run_cmd do
  let found:=(←getEnv).constants.toList.filter fun (n,_)=>
    n.toString.startsWith "_private.IngressAllocation.Bounded." && n.toString.endsWith ".IngressAllocation.all_bounded"
  match found with
  | [(n,.thmInfo ci)]=>
    logInfo m!"private-term|{n}|kind=theorem|type={ci.type}"
    modifyScope fun st=>{st with openDecls:=.explicit `acceptedBounded n::st.openDecls}
  | _=>throwError "Nonunique already checked accepted consumer {found.map Prod.fst}"
private theorem leaf_nonreject (k : Nat) :
    BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k false))≠(BodyIngress.machine k).reject:=by
  intro bad
  have equal:=congrArg Fin.val bad
  change 288+Cursor.stateCount k+6=328 at equal
  unfold Cursor.stateCount at equal
  omega
set_option maxRecDepth 4000 in
private theorem body_nonreject (k : Nat) (mode:Fin 3) :
    BodyIngress.body k (SerializedBody.entry mode)≠(BodyIngress.machine k).reject:=by
  intro bad
  have rejectEq: (BodyIngress.machine k).reject=BodyIngress.old k (CarryWindow.machine k).reject:=
    (BodyIngress.embeddings k).2.2.2.1
  exact (BodyIngress.embeddings k).2.2.2.2.2.2 _ mode (rejectEq.symm.trans bad.symm)
set_option maxRecDepth 4000 in
/-- Soundness of a literal reject at the first ingress event follows the
original accepted raw theorem, not an unproved geometric rejection shortcut. -/
private theorem reject_sound (k : Nat) {a m : Nat} (x:Bitstring a) (w:Bitstring m) (t : Nat)
    (hit:((BodyIngress.machine k).run t (initialConfig (BodyIngress.machine k)
      (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state=(BodyIngress.machine k).reject)
    (first:∀ u,u < t →
      (∀ b,((BodyIngress.machine k).run u (initialConfig (BodyIngress.machine k)
        (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state≠
          BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k b))) ∧
      (∀ mode:Fin 3,((BodyIngress.machine k).run u (initialConfig (BodyIngress.machine k)
        (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state≠
          BodyIngress.body k (SerializedBody.entry mode))) :
    PartAEndpoint.thresholdContentWitnessRelation k a m x w=false:=by
  cases truth:PartAEndpoint.thresholdContentWitnessRelation k a m x w with
  | false=>rfl
  | true=>
    obtain ⟨u,_heads,arrived⟩:=acceptedBounded k x w truth
    let c:=initialConfig (BodyIngress.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)
    have endSafe:((BodyIngress.machine k).run u c).state≠(BodyIngress.machine k).reject:=by
      rcases arrived with leaf | ⟨mode,body⟩
      · rw [leaf];exact leaf_nonreject k
      · rw [body];exact body_nonreject k mode
    by_cases early:u < t
    · rcases arrived with leaf | ⟨mode,body⟩
      · exact False.elim ((first u early).1 false leaf)
      · exact False.elim ((first u early).2 mode body)
    · have later:=(BodyIngress.machine k).run_reject_of_le c hit (by omega : t ≤ u)
      exact False.elim (endSafe ((congrArg Config.state later).trans hit))
end TotalIngressClosure
