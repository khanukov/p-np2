import RepairedFrontier.ProducerTarget
namespace RepairedFrontier
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Tactic
open FixedGammaTargetRegisterDecrement (borrow decBit)
set_option maxRecDepth 4000
attribute [local irreducible] UniformTM.run
/-- Proposition-only reconstruction of a finite register; no machine data. -/
private theorem finite_digits (f : Nat → Bool) (w : Nat) :
    ∃ v, v < 2^w ∧ ∀ i, i<w → v.testBit i=f i := by
  induction w with
  | zero => exact ⟨0,by decide,by intro i hi; omega⟩
  | succ w ih =>
    obtain ⟨v,hv,bits⟩ := ih
    have off : v.testBit w=false := Nat.testBit_lt_two_pow hv
    cases fw : f w with
    | false =>
      refine ⟨v,lt_trans hv (by simp [pow_succ]),?_⟩
      intro i hi
      by_cases eq : i=w
      · subst i; exact off.trans fw.symm
      · exact bits i (by omega)
    | true =>
      refine ⟨2^w+v,by simp [pow_succ]; omega,?_⟩
      intro i hi
      by_cases eq : i=w
      · subst i; rw [Nat.testBit_two_pow_add_eq,off]; exact fw.symm
      · rw [Nat.testBit_two_pow_add_gt (by omega)]
        exact bits i (by omega)
private theorem small_bound {a m : Nat} (x : Bitstring a) (w : Bitstring m) (n : Fin 3)
    (tag : FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (full : (if n.val=0 then 9 else 11) ≤ a+m)
    (h8 : FixedContentTagGate.physicalSymbol (Fin.append x w) 8=some (n.val==0))
    (h9 : n.val≠0 → FixedContentTagGate.physicalSymbol (Fin.append x w) 9=some true)
    (h10 : n.val≠0 → FixedContentTagGate.physicalSymbol (Fin.append x w) 10=some (n.val==2)) :
    ∃ t, t≤128*(pairLength a m+1)^2 ∧
      (SmallIngress.producer.run t (initialConfig SmallIngress.producer
        (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state=SmallIngress.producer.accept := by
  obtain ⟨t,_room,price,raw⟩ := SmallIngress.raw_small_physical x w n tag full h8 h9 h10
  have hit := congrArg (fun c => c.state.val) (raw 0)
  simp only [Nat.add_zero,UniformTM.run] at hit
  change (SmallIngress.machine.run t (initialConfig SmallIngress.machine
    (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state.val=288 at hit
  suffices found : ∃ u, u≤t ∧ (SmallIngress.producer.run u (initialConfig SmallIngress.producer
      (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state=SmallIngress.producer.accept by
    obtain ⟨u,hu,done⟩ := found
    exact ⟨u,hu.trans (price.trans (Nat.mul_le_mul_right _ (by decide : 64≤128))),done⟩
  by_contra no
  have absent (u : Nat) (hu : u≤t) : (SmallIngress.producer.run u (initialConfig SmallIngress.producer
      (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state≠SmallIngress.producer.accept :=
    fun h => no ⟨u,hu,h⟩
  have left := SmallIngress.producer.seq_run_left Stream.machine
    (initialConfig SmallIngress.producer (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))
    (fun u hu => absent u (by omega)) t le_rfl
  change SmallIngress.machine.run t (initialConfig SmallIngress.machine
    (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))=_ at left
  rw [left] at hit
  change (SmallIngress.producer.seqRoute Stream.machine _).val=288 at hit
  unfold UniformTM.seqRoute at hit
  split_ifs at hit with ha hr
  · exact absent t le_rfl ha
  · change (328:Nat)=288 at hit; omega
  · have lim := (SmallIngress.producer.run t (initialConfig SmallIngress.producer
      (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state.isLt
    change _ < 288 at lim
    change (SmallIngress.producer.run t (initialConfig SmallIngress.producer
      (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state.val=288 at hit
    omega
private theorem countdown_path {a m z C : Nat} {q : Fin FixedGammaPayloadDispatcher.stateCount}
    (x : Bitstring a) (w : Bitstring m)
    (tag : FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z) (wide : 2≤z)
    (first : FixedGammaPayloadDispatcherFirstArrival.StrictFirstTerminalAt
      (FixedRawLengthFence.allocation (pairLength a m)) x w C q) (s : Nat) :
    SmallIngress.producer.run (FixedRawLengthFence.h17RawClock a m z C (borrow x w z)+s)
      (initialConfig SmallIngress.producer (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))=
    SmallIngress.liftOld (FixedRawLengthFence.prefixed.run
      (FixedRawLengthFence.h17RawClock a m z C (borrow x w z)+s)
      (initialConfig FixedRawLengthFence.prefixed (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))) := by
  run_tac do
    let env ← getEnv
    let ns := env.constants.toList.map Prod.fst |>.filter fun n =>
      n.toString.startsWith "_private.RawFrontier.Capacity." && n.toString.endsWith ".RawFrontier.countdown_transport"
    unless ns.length==1 do throwError "Ambiguous countdown_transport: {ns}"
    let ast ← ofExcept (Parser.runParserCategory env `tactic "(exact OLD x w tag gamma wide first s)")
    evalTactic (ast.rewriteBottomUp fun stx =>
      if stx.isIdent && stx.getId.toString=="OLD" then mkIdent ns.head! else stx)
/-- Actual producer288 is bounded on every supported first read, including
later virtual payloads and capacity equality. No parse or acceptance premise. -/
theorem supported_producer {a m : Nat} (x : Bitstring a) (w : Bitstring m) (z : Nat)
    (tag : FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (physical : z=0 ∨ 9+z<a+m) :
    ∃ t, t≤128*(pairLength a m+1)^2 ∧
      ((SmallIngress.producer.run t (initialConfig SmallIngress.producer
        (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state=SmallIngress.producer.accept ∨
       (SmallIngress.producer.run t (initialConfig SmallIngress.producer
        (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state=SmallIngress.producer.reject) := by
  obtain ⟨support,term,zeros⟩ := (FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 z gamma
  by_cases hz0 : z=0
  · have full : 9≤a+m := by omega
    have h8 : FixedContentTagGate.physicalSymbol (Fin.append x w) 8=some true := by simpa [hz0] using term
    obtain ⟨t,price,done⟩ := small_bound x w ⟨0,by decide⟩ tag full h8 (by simp) (by simp)
    exact ⟨t,price,Or.inl done⟩
  by_cases hz1 : z=1
  · have full : 11≤a+m := by rcases physical with h | h <;> omega
    have h8 := zeros 0 (by omega : 0<z)
    have h9 : FixedContentTagGate.physicalSymbol (Fin.append x w) 9=some true := by simpa [hz1] using term
    let b := Fin.append x w ⟨10,by omega⟩
    have h10 : FixedContentTagGate.physicalSymbol (Fin.append x w) 10=some b := by
      simp [FixedContentTagGate.physicalSymbol,b,show 10<a+m by omega]
    cases hb : b with
    | false =>
      obtain ⟨t,price,done⟩ := small_bound x w ⟨1,by decide⟩ tag full h8 (by intro _; exact h9) (by intro _; simpa [hb] using h10)
      exact ⟨t,price,Or.inl done⟩
    | true =>
      obtain ⟨t,price,done⟩ := small_bound x w ⟨2,by decide⟩ tag full h8 (by intro _; exact h9) (by intro _; simpa [hb] using h10)
      exact ⟨t,price,Or.inl done⟩
  have wide : 2≤z := by omega
  obtain ⟨v,hv,bits⟩ := finite_digits (fun i => decBit x w z (borrow x w z) (z-i)) (z+1)
  have digits (j : Nat) (hj : j≤z) : v.testBit (z-j)=decBit x w z (borrow x w z) j := by
    simpa only [Nat.sub_sub_self hj] using bits (z-j) (by omega)
  have high : ∀ b, z<b → v.testBit b=false := (FixedGammaTargetUnaryCountdownIteration.high_iff_lt v z).2 hv
  let B := FixedRawLengthFence.allocation (pairLength a m)
  obtain ⟨C,q,price,first,_⟩ := FixedGammaPayloadDispatcherFirstArrival.tagged_strict_first_terminal (B := B) x w tag
  have resource := (FixedRawLengthFence.resource_bounds (pairLength a m)).1
  by_cases cap : v≤FixedRawLengthFence.capacity a m z
  · have old := FixedRawLengthFence.raw_fenced_countdown_success_exact x w resource tag gamma wide first digits high cap 0
    simp only [Nat.add_zero] at old
    have safe : (FixedRawLengthFence.prefixed.run
        (FixedRawLengthFence.countdownSuccessClock a m z C (borrow x w z) v)
        (initialConfig FixedRawLengthFence.prefixed B (encodePair x w))).state≠FixedRawLengthFence.prefixed.reject := by
      rw [old]; exact FixedRawLengthFence.prefixed.accept_ne_reject
    have path := SmallIngress.preserves_nonreject _ _ safe
    change SmallIngress.producer.run _ (initialConfig SmallIngress.producer B (encodePair x w))=_ at path
    rw [old] at path
    refine ⟨_,(FixedRawLengthFence.countdown_clock_bound (by omega) wide (FixedGammaTargetRegisterDecrement.borrow_pins x w z).1 price cap).1,Or.inl ?_⟩
    rw [path]; rfl
  · have overflow : FixedRawLengthFence.capacity a m z<v := by omega
    have old := FixedRawLengthFence.raw_fenced_countdown_reject_exact x w resource tag gamma wide first digits high overflow 0
    simp only [Nat.add_zero] at old
    let d := (borrow x w z+2)+FixedGammaTargetUnaryCountdownIteration.roundsClock z 0 (FixedRawLengthFence.capacity a m z)+
      (2*z+FixedRawLengthFence.capacity a m z+6)
    have clock : FixedRawLengthFence.countdownRejectClock a m z C (borrow x w z)=FixedRawLengthFence.h17RawClock a m z C (borrow x w z)+d := by
      dsimp [d,FixedRawLengthFence.countdownRejectClock]; omega
    have path := countdown_path x w tag gamma wide first d
    rw [←clock,old] at path
    refine ⟨_,(FixedRawLengthFence.countdown_clock_bound (v := 0) (by omega) wide (FixedGammaTargetRegisterDecrement.borrow_pins x w z).1 price (Nat.zero_le _)).2.1,Or.inr ?_⟩
    rw [path]; rfl
end RepairedFrontier
