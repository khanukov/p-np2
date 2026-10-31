import IngressAllocation.RawCountdown
import IngressAllocation.Producer
namespace IngressAllocation
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command
attribute [local irreducible] UniformTM.run
run_cmd do
  let found:=(← getEnv).constants.toList.filter fun (n,_) =>
    n.toString.startsWith "_private.IngressAllocation.RawCountdown." &&
      n.toString.endsWith ".IngressAllocation.CountdownPrefix.raw_success_heads"
  match found with
  | [(n,.thmInfo ci)] =>
    logInfo m!"private-term|{n}|kind=theorem|type={ci.type}"
    modifyScope fun st => {st with openDecls:=.explicit `countdownHeads n :: st.openDecls}
  | _=>throwError "Nonunique raw countdown trace: {found.map Prod.fst}"
private theorem large_producer_first (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    {pr : AcceptedBody.Parsed k}
    (parsed : contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr)
    (tag : FixedContentTagGate.tagMatches (Fin.append x w)=true) (large : 3 ≤ pr.2.n) :
    let R:=pairLength a m;let B:=FixedRawLengthFence.allocation R
    ∃ z,2 ≤ z ∧ FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z ∧
      (pr.2.n < FixedRawLengthFence.capacity a m z →
        ∃ (t : Nat) (hL : a+m+z+2 < tapeLength R B),t ≤ FixedRawLengthFence.countdownDeadline R ∧
          SmallIngress.producer.run t (initialConfig SmallIngress.producer B (encodePair x w))=
            ⟨SmallIngress.producer.accept,⟨a+m+z+2,hL⟩,FixedRawLengthFence.countdownTape B x w z 0 pr.2.n⟩ ∧
          (∀ u,u < t → (SmallIngress.producer.run u (initialConfig SmallIngress.producer B (encodePair x w))).state ≠
            SmallIngress.producer.accept) ∧
          ∀ u,u ≤ t → (SmallIngress.producer.run u
            (initialConfig SmallIngress.producer B (encodePair x w))).head.val ≤ 12*(R+1)^2) := by
  intro R B
  obtain ⟨consumed,header,target⟩:=contentInput?_target_eq_contentHeader
    (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w) parsed
  rw [← target] at header
  obtain ⟨z,gamma,consumedEq,_range,value,_fit,digits,high⟩:=decremented_register_digits x w header
  have hz : 2 ≤ z := by
    by_contra small
    have upper : 2^(z+1) ≤ (2:Nat)^2:=Nat.pow_le_pow_right (by decide) (by omega)
    norm_num at upper
    omega
  obtain ⟨C,q,hC,first,_time,_config⟩:=FixedRawLengthFence.raw_fenced_h17_allocated x w tag gamma hz
  refine ⟨z,hz,gamma,?_⟩
  intro cap
  have room:=(FixedRawLengthFence.resource_bounds R).1
  have digitValue : ∀ j,j ≤ z → pr.2.n.testBit (z-j)=
      FixedGammaTargetRegisterDecrement.decBit x w z (FixedGammaTargetRegisterDecrement.borrow x w z) j :=
    fun j hj=>(digits j hj).symm
  let time:=FixedRawLengthFence.countdownSuccessClock a m z C
    (FixedGammaTargetRegisterDecrement.borrow x w z) pr.2.n
  let old:=initialConfig FixedRawLengthFence.prefixed B (encodePair x w)
  let own:=initialConfig SmallIngress.producer B (encodePair x w)
  have fitL : a+m+z+2 < tapeLength R B := by
    have width:=((FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 z gamma).1
    have sourceWidth : a+m ≤ R := by dsimp only [R,pairLength];omega
    change a+m+z+2 < R+B+1
    omega
  have finish : FixedRawLengthFence.prefixed.run time old=
      ⟨FixedRawLengthFence.prefixed.accept,⟨a+m+z+2,fitL⟩,
        FixedRawLengthFence.countdownTape B x w z 0 pr.2.n⟩ := by
    have actual:=FixedRawLengthFence.raw_fenced_countdown_success_exact x w room tag gamma hz first
      digitValue high (Nat.le_of_lt cap) 0
    rw [Nat.add_zero] at actual
    exact actual.trans (by
      apply Config.ext_parts
      · rfl
      · apply Fin.ext
        change a+m+2+z=a+m+z+2
        omega
      · rfl)
  have oldSafe (u : Nat) (hu : u ≤ time) :
      (FixedRawLengthFence.prefixed.run u old).state ≠ FixedRawLengthFence.prefixed.reject := by
    intro rejected
    have same:=FixedRawLengthFence.prefixed.run_reject_of_le old rejected hu
    have lastReject:=(congrArg Config.state same).trans rejected
    rw [finish] at lastReject
    exact FixedRawLengthFence.prefixed.accept_ne_reject lastReject
  have tx (u : Nat) (hu : u ≤ time) : SmallIngress.producer.run u own=
      SmallIngress.liftOld (FixedRawLengthFence.prefixed.run u old) :=
    SmallIngress.preserves_nonreject old u (oldSafe u hu)
  have done : SmallIngress.producer.run time own=
      ⟨SmallIngress.producer.accept,⟨a+m+z+2,fitL⟩,
        FixedRawLengthFence.countdownTape B x w z 0 pr.2.n⟩ := by
    rw [tx time le_rfl,finish]
    rfl
  have footprint (u : Nat) (hu : u ≤ time) :
      (SmallIngress.producer.run u own).head.val ≤ 12*(R+1)^2 := by
    rw [tx u hu]
    exact countdownHeads x w tag gamma hz first digitValue high cap u hu
  have width : 9+z ≤ a+m := by
    have h:=((FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 z gamma).1
    omega
  have clock : time ≤ FixedRawLengthFence.countdownDeadline R :=
    (FixedRawLengthFence.countdown_clock_bound width hz
      (FixedGammaTargetRegisterDecrement.borrow_pins x w z).1 hC (Nat.le_of_lt cap)).1
  obtain ⟨t,ht,early,endRun⟩:=Body.first_accept_whole SmallIngress.producer own _ _ done rfl
  exact ⟨t,fitL,ht.trans clock,endRun,early,fun u hu=>footprint u (hu.trans ht)⟩
end IngressAllocation
