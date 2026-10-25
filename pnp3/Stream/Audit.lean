import Stream.Kernel
namespace Stream.Audit
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
open Stream Stream.Target Stream.RawTarget
set_option maxRecDepth 40000
def pin_q (i : Nat) : Fin 64 :=
  @Stream.q i
def pin_unpaid (mode : Fin 3) : Fin 64 :=
  @Stream.unpaid mode
def pin_paid (mode : Fin 3) : Fin 64 :=
  @Stream.paid mode
def pin_rows (s : Fin 64) (b : Option Bool) : Fin 64 × Option Bool × Move :=
  @Stream.rows s b
def pin_machine  : UniformTM :=
  @Stream.machine
def pin_rawMachine  : UniformTM :=
  @Stream.rawMachine
def pin_Target_cursor (A S r : Nat) : Nat :=
  @Stream.Target.cursor A S r
def pin_Target_mode (U : Nat → Option Bool) (p S : Nat) : Fin 3 :=
  @Stream.Target.mode U p S
def pin_Target_image (U : Nat → Option Bool) (S z n A r marks : Nat) (lift : Bool) : Nat → Option Bool :=
  @Stream.Target.image U S z n A r marks lift
def pin_Target_Kernel  : Prop :=
  @Stream.Target.Kernel
def pin_Target_PartA (partAMachine : Nat → UniformTM) (partAExponent : Nat → Nat) : Prop :=
  @Stream.Target.PartA partAMachine partAExponent
theorem check_raw_budget_cells {a m z n : Nat} (x : Bitstring a) (w : Bitstring m)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (room : n < FixedRawLengthFence.capacity a m z) : a+m+z+n+3 < FixedRawLengthFence.fencePos (pairLength a m) ∧
    (∀ i : Fin (tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m))),
      a+m+z+n+3 ≤ i.val → i.val < FixedRawLengthFence.fencePos (pairLength a m) →
      Body.installedTape (FixedRawLengthFence.countdownTape
        (FixedRawLengthFence.allocation (pairLength a m)) x w z 0 n) (a+m+z+2) n i=none) ∧
    ∃ hf : FixedRawLengthFence.fencePos (pairLength a m) <
        tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m)),
      Body.installedTape (FixedRawLengthFence.countdownTape
        (FixedRawLengthFence.allocation (pairLength a m)) x w z 0 n) (a+m+z+2) n
          ⟨FixedRawLengthFence.fencePos (pairLength a m),hf⟩=some false :=
  @Stream.raw_budget_cells a m z n x w gamma room
theorem check_accepted_budget {a m z n : Nat} (shape : m=a+1) (hz : z≤a+m) (hn : n≤a+m) : a+m ≤ FixedRawLengthFence.fencePos (pairLength a m)-(a+m+z+n+3)-1 :=
  @Stream.accepted_budget a m z n shape hz hn
theorem check_accepted_rows_fit (k : Nat) {a m z : Nat} (x : Bitstring a) (w : Bitstring m)
    (accepted : PartAEndpoint.thresholdContentWitnessRelation k a m x w=true)
    {pr : AcceptedBody.Parsed k}
    (parsed : contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z) : 2^pr.2.n ≤ FixedRawLengthFence.fencePos (pairLength a m)-(a+m+z+pr.2.n+3)-1 :=
  @Stream.accepted_rows_fit k a m z x w accepted pr parsed gamma
def pin_RawTarget_AcceptedOrbit (k : Nat) : Prop :=
  @Stream.RawTarget.AcceptedOrbit k
def pin_BodyTarget_Orbit (k : Nat) : Prop :=
  @Stream.BodyTarget.Orbit k
theorem check_kernel  : ∀ (N B S z n A F : Nat) (U : Nat → Option Bool),
    2 ≤ A → A ≤ S → S+z+n+3 < F → F < tapeLength N B →
    (∀ i, A ≤ i → i < S → ∃ b, U i=some b) → U S=none →
    (∀ i, S < i → i < S+z+2 → U i=some false) → U (S+z+2)=none →
    U (S+z+n+3)=none →
    (∀ i, S+z+n+3 < i → i < F → U i=none) → U F=some false →
    let H := S+z+n+3
    let cap := F-H-1
    let count := min (2^n) cap
    ∀ hH : H < tapeLength N B,
    let c : Config machine.stateCount N B :=
      ⟨unpaid (mode U A S),⟨H,hH⟩,fun i => image U S z n A 0 0 true i.val⟩
    ∃ T, T ≤ 64*(F+1)^2 ∧
      (∀ r, r<count → ∃ t, t ≤ T ∧
        machine.run t c = ⟨paid (mode U (cursor A S r) S),⟨H,hH⟩,
          fun i => image U S z n A r (r+1) true i.val⟩) ∧
      (if 2^n ≤ cap then
        ∃ hp : cursor A S (2^n) < tapeLength N B,
          machine.run T c =
            ⟨q (if cursor A S (2^n)=S then 57 else 58),⟨cursor A S (2^n),hp⟩,
              fun i => image U S z n A (2^n) (2^n) false i.val⟩
       else
        ∃ hF : F < tapeLength N B,
          machine.run T c = ⟨machine.reject,⟨F,hF⟩,
            fun i => image U S z n A cap cap true i.val⟩) :=
  @Stream.kernel
theorem check_raw_body (k : Nat) : ∀ {a m : Nat} (x : Bitstring a) (w : Bitstring m) {pr : (Sigma fun r : Nat => PrefixInput (treeMCSPSearchProblem (thresholdPoly k) (TreeMCSPSearchWitnessEncoding.ofCodec (treeCircuitWitnessCodec (thresholdPoly k)))) (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) r))},
    contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr →
    FixedContentTagGate.tagMatches (Fin.append x w)=true → 3 ≤ pr.2.n →
    ∃ z, 2 ≤ z ∧ FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z ∧
      (pr.2.n < FixedRawLengthFence.capacity a m z → 9+2*z ≤ a+m →
        ∃ (T : Nat) (hH : a+m+z+pr.2.n+3 < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m))),
          T ≤ 2048*(pairLength a m+1)^2 ∧
          let U := Body.extend (Body.installedTape (FixedRawLengthFence.countdownTape
            (FixedRawLengthFence.allocation (pairLength a m)) x w z 0 pr.2.n) (a+m+z+2) pr.2.n)
          let F := FixedRawLengthFence.fencePos (pairLength a m)
          let cap := F-(a+m+z+pr.2.n+3)-1
          (∀ r, r < min (2^pr.2.n) cap → ∃ t, t ≤ T ∧
            rawMachine.run t (initialConfig rawMachine (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)) =
              FixedRawLengthFence.prefixed.seqEmbedRight machine
                ⟨paid (Target.mode U (Target.cursor (9+2*z) (a+m) r) (a+m)),⟨a+m+z+pr.2.n+3,hH⟩,
                  fun i => Target.image U (a+m) z pr.2.n (9+2*z) r (r+1) true i.val⟩) ∧
          (if 2^pr.2.n ≤ cap then
            ∃ hp : Target.cursor (9+2*z) (a+m) (2^pr.2.n) < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m)),
              rawMachine.run T (initialConfig rawMachine (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)) =
                FixedRawLengthFence.prefixed.seqEmbedRight machine
                  ⟨q (if Target.cursor (9+2*z) (a+m) (2^pr.2.n)=a+m then 57 else 58),⟨Target.cursor (9+2*z) (a+m) (2^pr.2.n),hp⟩,
                    fun i => Target.image U (a+m) z pr.2.n (9+2*z) (2^pr.2.n) (2^pr.2.n) false i.val⟩
           else ∃ hF : F < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m)),
              rawMachine.run T (initialConfig rawMachine (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)) =
                FixedRawLengthFence.prefixed.seqEmbedRight machine ⟨machine.reject,⟨F,hF⟩,
                  fun i => Target.image U (a+m) z pr.2.n (9+2*z) cap cap true i.val⟩)) :=
  @Stream.raw_body k
theorem check_raw_accepted (k : Nat) : ∀ {a m : Nat} (x : Bitstring a) (w : Bitstring m),
    PartAEndpoint.thresholdContentWitnessRelation k a m x w=true →
    ∃ pr : (Sigma fun r : Nat => PrefixInput (treeMCSPSearchProblem (thresholdPoly k) (TreeMCSPSearchWitnessEncoding.ofCodec (treeCircuitWitnessCodec (thresholdPoly k)))) (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) r)),
      contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr ∧
      Pnp3.Models.Partial.tableLen pr.2.n ≤ a+m ∧
      (3 ≤ pr.2.n → ∃ (z T : Nat)
        (hH : a+m+z+pr.2.n+3 < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m))),
        FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z ∧
        T ≤ 2048*(pairLength a m+1)^2 ∧
        let U := Body.extend (Body.installedTape (FixedRawLengthFence.countdownTape
          (FixedRawLengthFence.allocation (pairLength a m)) x w z 0 pr.2.n) (a+m+z+2) pr.2.n)
        (∀ r, r<2^pr.2.n → ∃ t, t ≤ T ∧
          rawMachine.run t (initialConfig rawMachine (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)) =
            FixedRawLengthFence.prefixed.seqEmbedRight machine
              ⟨paid (Target.mode U (Target.cursor (9+2*z) (a+m) r) (a+m)),⟨a+m+z+pr.2.n+3,hH⟩,
                fun i => Target.image U (a+m) z pr.2.n (9+2*z) r (r+1) true i.val⟩) ∧
        ∃ hp : Target.cursor (9+2*z) (a+m) (2^pr.2.n) <
          tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m)),
          rawMachine.run T (initialConfig rawMachine (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)) =
            FixedRawLengthFence.prefixed.seqEmbedRight machine
              ⟨q (if Target.cursor (9+2*z) (a+m) (2^pr.2.n)=a+m then 57 else 58),
                ⟨Target.cursor (9+2*z) (a+m) (2^pr.2.n),hp⟩,
                fun i => Target.image U (a+m) z pr.2.n (9+2*z) (2^pr.2.n) (2^pr.2.n) false i.val⟩) :=
  @Stream.raw_accepted k
#print axioms Stream.q
#print axioms Stream.Audit.pin_q
#print axioms Stream.unpaid
#print axioms Stream.Audit.pin_unpaid
#print axioms Stream.paid
#print axioms Stream.Audit.pin_paid
#print axioms Stream.rows
#print axioms Stream.Audit.pin_rows
#print axioms Stream.machine
#print axioms Stream.Audit.pin_machine
#print axioms Stream.rawMachine
#print axioms Stream.Audit.pin_rawMachine
#print axioms Stream.Target.cursor
#print axioms Stream.Audit.pin_Target_cursor
#print axioms Stream.Target.mode
#print axioms Stream.Audit.pin_Target_mode
#print axioms Stream.Target.image
#print axioms Stream.Audit.pin_Target_image
#print axioms Stream.Target.Kernel
#print axioms Stream.Audit.pin_Target_Kernel
#print axioms Stream.Target.PartA
#print axioms Stream.Audit.pin_Target_PartA
#print axioms Stream.raw_budget_cells
#print axioms Stream.Audit.check_raw_budget_cells
#print axioms Stream.accepted_budget
#print axioms Stream.Audit.check_accepted_budget
#print axioms Stream.accepted_rows_fit
#print axioms Stream.Audit.check_accepted_rows_fit
#print axioms Stream.RawTarget.AcceptedOrbit
#print axioms Stream.Audit.pin_RawTarget_AcceptedOrbit
#print axioms Stream.BodyTarget.Orbit
#print axioms Stream.Audit.pin_BodyTarget_Orbit
#print axioms Stream.kernel
#print axioms Stream.Audit.check_kernel
#print axioms Stream.raw_body
#print axioms Stream.Audit.check_raw_body
#print axioms Stream.raw_accepted
#print axioms Stream.Audit.check_raw_accepted
#guard machine.stateCount=64
#guard rawMachine.stateCount=320
#guard rawMachine.reject.val=296
end Stream.Audit
