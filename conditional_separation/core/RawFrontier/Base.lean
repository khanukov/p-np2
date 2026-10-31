import RawFrontier.Target
namespace RawFrontier
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
set_option maxRecDepth 4000
attribute [local irreducible] UniformTM.run
/-- Same-machine soundness at an EARLY reject, before either live work row.
It uses W's actual accepted raw handoff, not a separate parser model. -/
theorem early_reject_sound (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m) (t : Nat)
    (reject : ((AllArityCursor.machine k).run t (initialConfig (AllArityCursor.machine k)
      (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state=(AllArityCursor.machine k).reject)
    (noWork : ∀ u, u < t →
      ((AllArityCursor.machine k).run u (initialConfig (AllArityCursor.machine k)
        (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state≠
          SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k 57) ∧
      ((AllArityCursor.machine k).run u (initialConfig (AllArityCursor.machine k)
        (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state≠
          SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k 58)) :
    PartAEndpoint.thresholdContentWitnessRelation k a m x w=false := by
  cases hrel : PartAEndpoint.thresholdContentWitnessRelation k a m x w with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨pr,_parsed,_table,z,T,_hH,_gamma,_price,_hp,pre,_prefix,_physical,_eof⟩ :=
      AllArityWorkspace.accepted_raw k x w hrel
    have endpoint := congrArg Config.state pre
    have work : ((AllArityCursor.machine k).run T (initialConfig (AllArityCursor.machine k)
        (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state=
          SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k 57) ∨
        ((AllArityCursor.machine k).run T (initialConfig (AllArityCursor.machine k)
        (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state=
          SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k 58) := by
      split_ifs at endpoint <;> tauto
    by_cases early : T < t
    · rcases work with h | h
      · exact (noWork T early).1 h
      · exact (noWork T early).2 h
    · have same := (AllArityCursor.machine k).run_reject_of_le _ reject (by omega : t ≤ T)
      have eq := congrArg Config.state same
      rw [reject] at eq
      rcases work with h | h
      all_goals
        have val := congrArg Fin.val (eq.symm.trans h)
        rw [(AllArityCursor.control_values k).2.2.2] at val
        simp only [(AllArityCursor.control_values k).1,(AllArityCursor.control_values k).2.1] at val
        omega
private theorem first_reject (M : UniformTM) {N B : Nat} (c : Config M.stateCount N B)
    (T : Nat) (hit : (M.run T c).state=M.reject) :
    ∃ t, t ≤ T ∧ (M.run t c).state=M.reject ∧ ∀ u, u < t → (M.run u c).state≠M.reject := by
  induction T with
  | zero => exact ⟨0,le_rfl,hit,by intro u hu; omega⟩
  | succ T ih =>
    by_cases prior : (M.run T c).state=M.reject
    · obtain ⟨t,ht,he,first⟩ := ih prior
      exact ⟨t,by omega,he,first⟩
    · refine ⟨T+1,le_rfl,hit,?_⟩
      intro u hu h
      have same := M.run_reject_of_le c h (by omega : u ≤ T)
      exact prior (by rw [same]; exact h)
private theorem route_bound (k : Nat) (s : Fin SmallIngress.producer.stateCount) :
    (SmallIngress.producer.seqRoute (Cursor.machine k) s).val < 345 := by
  unfold UniformTM.seqRoute
  split_ifs
  · change 288+0 < 345
    decide
  · have e : (SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.machine k).reject).val=328 :=
      (AllArityCursor.control_values k).2.2.2
    rw [e]; decide
  · exact s.isLt.trans_le (by decide)
/-- Raw-origin conversion of a bounded ACTUAL producer288 reject. Connected
syntactic/capacity theorems below discharge the producer premise. -/
theorem producer_reject_frontier (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m) (T : Nat)
    (price : T ≤ 128*(pairLength a m+1)^2)
    (hit : (SmallIngress.producer.run T (initialConfig SmallIngress.producer
      (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state=SmallIngress.producer.reject) :
    let c := initialConfig (AllArityCursor.machine k)
      (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)
    ∃ t, t ≤ 128*(pairLength a m+1)^2 ∧
      ((AllArityCursor.machine k).run t c).state=(AllArityCursor.machine k).reject ∧
      (∀ u, u < t →
        ((AllArityCursor.machine k).run u c).state≠(AllArityCursor.machine k).reject ∧
        ((AllArityCursor.machine k).run u c).state≠SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k 57) ∧
        ((AllArityCursor.machine k).run u c).state≠SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k 58)) ∧
      (∀ u, u ≤ t → ((AllArityCursor.machine k).run u c).state≠(AllArityCursor.machine k).accept) ∧
      PartAEndpoint.thresholdContentWitnessRelation k a m x w=false := by
  dsimp only
  let B := FixedRawLengthFence.allocation (pairLength a m)
  let c := initialConfig (AllArityCursor.machine k) B (encodePair x w)
  let p := initialConfig SmallIngress.producer B (encodePair x w)
  have noAccept : ∀ u, u < T → (SmallIngress.producer.run u p).state≠SmallIngress.producer.accept := by
    intro u hu h
    have same := SmallIngress.producer.run_accept_of_le p h (by omega : u ≤ T)
    have bad := hit
    rw [same,h] at bad
    exact SmallIngress.producer.accept_ne_reject bad
  have done := SmallIngress.producer.seq_reject_handoff (Cursor.machine k) p hit 0
  have done' : ((AllArityCursor.machine k).run T c).state=(AllArityCursor.machine k).reject :=
    congrArg Config.state done
  have noWork (u : Nat) (hu : u ≤ T) : ((AllArityCursor.machine k).run u c).state≠
      SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k 57) ∧
      ((AllArityCursor.machine k).run u c).state≠
      SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k 58) := by
    have path := SmallIngress.producer.seq_run_left (Cursor.machine k) p noAccept u hu
    have lim := route_bound k (SmallIngress.producer.run u p).state
    have ev := congrArg (fun c => c.state.val) path
    change ((AllArityCursor.machine k).run u c).state.val=
      (SmallIngress.producer.seqRoute (Cursor.machine k) (SmallIngress.producer.run u p).state).val at ev
    rw [←ev] at lim
    constructor <;> intro h
    all_goals
      rw [h] at lim
      simp only [(AllArityCursor.control_values k).1,(AllArityCursor.control_values k).2.1] at lim
      omega
  obtain ⟨t,ht,reject,first⟩ := first_reject (AllArityCursor.machine k) c T done'
  have safe (u : Nat) (hu : u ≤ t) : ((AllArityCursor.machine k).run u c).state≠(AllArityCursor.machine k).accept := by
    intro h
    have same := (AllArityCursor.machine k).run_accept_of_le c h hu
    rw [same,h] at reject
    exact (AllArityCursor.machine k).accept_ne_reject reject
  refine ⟨t,ht.trans price,reject,?_,safe,early_reject_sound k x w t reject ?_⟩
  · intro u hu
    exact ⟨first u hu,(noWork u (by omega)).1,(noWork u (by omega)).2⟩
  · intro u hu
    exact noWork u (by omega)
end RawFrontier
