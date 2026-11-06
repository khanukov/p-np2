import Body.Proof
import Pnp4.Frontier.ContractExpansion.ContentRawFencedDecrementBridge
namespace Body
open Pnp3.Complexity.Uniform.V1
open Pnp4.Frontier.ContractExpansion
open Pnp4.Frontier Pnp4.AlgorithmsToLowerBounds
open PairEncoding
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

def installedTape {N B : Nat} (T : Fin (tapeLength N B) → Option Bool) (left n : Nat) :=
  fun i : Fin (tapeLength N B) =>
    if left < i.val ∧ i.val < left+n+1 then some false else T i

/-- Arbitrary exterior tape. Every prepared mark is read; no clean scratch premise. -/
theorem install_exact {N B : Nat} (left n : Nat) (c : Config machine.stateCount N B)
    (hp : left+n+1 < tapeLength N B) (hq : c.state=machine.start) (hh : c.head.val=left)
    (hl : c.tape ⟨left,by omega⟩=none)
    (hr : c.tape ⟨left+n+1,hp⟩=none)
    (marks : ∀ i : Fin (tapeLength N B), left < i.val → i.val < left+n+1 → c.tape i=some true) :
    machine.run (n+2) c = ⟨q 2,⟨left+n+1,hp⟩,installedTape c.tape left n⟩ ∧
    Target.Span (installedTape c.tape left n) left (List.replicate n false) := by
  let T := extend c.tape
  have hleft : T left=none := by simpa [T,extend,show left < tapeLength N B by omega] using hl
  have hright : T (left+n+1)=none := by simpa [T,extend,hp] using hr
  have path := install_path T left n hleft (by
    intro i h1 h2
    have hi : i < tapeLength N B := by omega
    simpa [T,extend,hi] using marks ⟨i,hi⟩ h1 h2) hright
  have he := path.execute hp
  have hc : embed (N := N) (B := B) ⟨machine.start,left,T⟩ (by change left < tapeLength N B; omega) = c := by
    apply Config.ext_parts hq.symm (Fin.ext hh.symm)
    funext i; exact extend_read c.tape i
  rw [hc] at he
  constructor
  · rw [he]
    apply Config.ext_parts
    · rfl
    · rfl
    · funext i
      change clear T (left+1) n i.val = installedTape c.tape left n i
      simp only [clear,installedTape]
      have hi : left+1 ≤ i.val ↔ left < i.val := by omega
      have heq : left+1+n=left+n+1 := by omega
      simp only [hi,heq]
      split_ifs <;> first | rfl | exact extend_read c.tape i
  · intro i
    simp only [List.length_replicate]
    refine ⟨?_,?_,?_⟩
    · intro hi
      rw [installedTape,if_neg (by omega)]
      exact (congrArg c.tape (Fin.ext hi)).trans hl
    · intro hi
      rw [installedTape,if_neg (by omega)]
      exact (congrArg c.tape (Fin.ext hi)).trans hr
    · intro j hj hij
      have lo : left < i.val := by omega
      have up : i.val < left+n+1 := by omega
      simp [installedTape,lo,up,hj]

/-- First arrival is derived from the actual run; absorption yields whole Config
identity, not just state equality. No data is extracted to construct a machine. -/
theorem first_accept_whole (M : UniformTM) {N B : Nat} (c : Config M.stateCount N B)
    (deadline : Nat) (endConfig : Config M.stateCount N B)
    (he : M.run deadline c=endConfig) (ha : endConfig.state=M.accept) :
    ∃ T, T ≤ deadline ∧ (∀ t, t < T → (M.run t c).state≠M.accept) ∧ M.run T c=endConfig := by
  have ex : ∃ t, (M.run t c).state=M.accept := ⟨deadline,by rw [he]; exact ha⟩
  let T := Nat.find ex
  have ht : T ≤ deadline := Nat.find_min' ex (by rw [he]; exact ha)
  have hacc : (M.run T c).state=M.accept := Nat.find_spec ex
  refine ⟨T,ht,?_,?_⟩
  · intro t hlt; exact Nat.find_min ex hlt
  · rw [← M.run_accept_of_le c hacc ht,he]

/-- Raw-origin capstone. The same parsed target supplies every unary mark and
all blank/boundary premises. The first accepting producer arrival hands over the
WHOLE configuration; all later body times are actual runs of ONE fixed table.
Strict capacity is explicit; no semantic false claim is made for capacity reject. -/
theorem raw_counter_parsed (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    {pr : Sigma fun r : Nat =>
      PrefixInput (treeMCSPSearchProblem (thresholdPoly k)
        (TreeMCSPSearchWitnessEncoding.ofCodec (treeCircuitWitnessCodec (thresholdPoly k))))
        (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) r)}
    (hpr : contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w)=true) (hn : 3 ≤ pr.2.n) :
    let B := FixedRawLengthFence.allocation (pairLength a m)
    pr.2.n=pr.1 ∧ ∃ z,
      2 ≤ z ∧ FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z ∧
      (pr.2.n < FixedRawLengthFence.capacity a m z →
        ∃ (T : Nat) (hR : a+m+2+z+pr.2.n+1 < tapeLength (pairLength a m) B),
          T ≤ FixedRawLengthFence.countdownDeadline (pairLength a m) ∧
          let startTape := FixedRawLengthFence.countdownTape B x w z 0 pr.2.n
          let ready : Config machine.stateCount (pairLength a m) B :=
            ⟨q 2,⟨a+m+2+z+pr.2.n+1,hR⟩,installedTape startTape (a+m+2+z) pr.2.n⟩
          Target.Span ready.tape (a+m+2+z) (List.replicate pr.2.n false) ∧
          (∀ i : Fin (tapeLength (pairLength a m) B), i.val ≤ a+m+2+z ∨ a+m+2+z+pr.2.n+1 ≤ i.val → ready.tape i=startTape i) ∧
          ∀ s, rawMachine.run (T+pr.2.n+2+s)
            (initialConfig rawMachine B (encodePair x w)) =
              FixedRawLengthFence.prefixed.seqEmbedRight machine (machine.run s ready)) := by
  dsimp only
  obtain ⟨hnr,z,C,qp,hS,hz,hg,_hh,hC,_hfirst,success,_reject⟩ :=
    raw_fenced_countdown_parsed_target k x w hpr htag hn
  refine ⟨hnr,z,hz,hg,?_⟩
  intro hcap
  have hr := (FixedRawLengthFence.resource_bounds (pairLength a m)).1
  obtain ⟨price,he⟩ := success (Nat.le_of_lt hcap)
  let B := FixedRawLengthFence.allocation (pairLength a m)
  let n := pr.2.n
  let L := a+m+2+z
  let tape := FixedRawLengthFence.countdownTape B x w z 0 n
  have cells := FixedRawLengthFence.countdown_success_cells x w hg hr (Nat.le_of_lt hcap)
  have geo : a+m+3+z+FixedRawLengthFence.capacity a m z=FixedRawLengthFence.fencePos (pairLength a m) := by
    have hw := ((FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 z hg).1
    simp only [FixedRawLengthFence.capacity,FixedRawLengthFence.fencePos,pairLength] at *; omega
  have fit := (FixedRawLengthFence.installed_cells (encodePair x w) hr).2
  have hR : L+n+1 < tapeLength (pairLength a m) B := by
    have hf : FixedRawLengthFence.fencePos (pairLength a m) < tapeLength (pairLength a m) B := by
      dsimp [FixedRawLengthFence.fencePos,tapeLength,B,pairLength] at *; omega
    dsimp [L,n]; omega
  let entry : Config machine.stateCount (pairLength a m) B := ⟨machine.start,⟨L,hS⟩,tape⟩
  have hleft : entry.tape ⟨L,by omega⟩=none := cells.2.2.1 _ rfl
  have hright : entry.tape ⟨L+n+1,hR⟩=none := cells.2.2.2.2.1 _ (by dsimp [L,n]; omega) (by dsimp [L,n]; omega)
  have marks : ∀ i : Fin (tapeLength (pairLength a m) B), L < i.val → i.val < L+n+1 → entry.tape i=some true := by
    intro i h1 h2; exact cells.2.2.2.1 i (by dsimp [L] at *; omega) (by dsimp [L,n] at *; omega)
  obtain ⟨install,span⟩ := install_exact L n entry hR rfl rfl hleft hright marks
  obtain ⟨T,hT,first,arrived⟩ := first_accept_whole FixedRawLengthFence.prefixed
    (initialConfig FixedRawLengthFence.prefixed B (encodePair x w)) _ _ he rfl
  refine ⟨T,hR,hT.trans price,span,?_,?_⟩
  · intro i hi
    change installedTape tape L n i=tape i
    simp only [installedTape]
    rw [if_neg (by dsimp [L,n] at *; omega)]
  · intro s
    have hand := FixedRawLengthFence.prefixed.seq_handoff machine
      (initialConfig FixedRawLengthFence.prefixed B (encodePair x w)) first
      (by rw [arrived]) (n+2+s)
    rw [arrived] at hand
    change rawMachine.run (T+(n+2+s)) (initialConfig rawMachine B (encodePair x w)) = _ at hand
    rw [machine.run_add,install] at hand
    simpa only [entry,tape,L,n,B,Nat.add_assoc] using hand

theorem zero_value (n : Nat) : value (List.replicate n false)=0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,value,ih]

/-- The producer consumes gamma cells, but every serialized source cell after
that header remains literal data. This is the source region preserved on reentry. -/
theorem raw_source_after_header {a m B z n : Nat} (x : Bitstring a) (w : Bitstring m)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (hr : 2*pairLength a m+2 ≤ B) (hn : n ≤ FixedRawLengthFence.capacity a m z)
    (i : Fin (tapeLength (pairLength a m) B)) (lo : 8+2*z+1 ≤ i.val) (hi : i.val < a+m) :
    FixedRawLengthFence.countdownTape B x w z 0 n i = some (Fin.append x w ⟨i.val,hi⟩) := by
  rw [(FixedRawLengthFence.countdown_success_cells x w hg hr hn).1 i hi]
  have hw : FixedGammaTargetPayloadExhaustion.termWalk (a+m) z ≤ z := Nat.min_le_left _ _
  unfold FixedGammaTargetPayloadExhaustion.finishTape
  rw [if_neg (by omega),if_neg (by omega),if_neg (by omega)]
  simp [FixedPairContentMarkerErase.contentTape,hi]

/-- Arbitrarily many raw-origin counter rounds, with literal serialized source
preservation at EVERY reentry. Neither work exhaustion nor this theorem evaluates
a tree or decides the target relation. -/
theorem raw_repeated_parsed (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    {pr : Sigma fun r : Nat =>
      PrefixInput (treeMCSPSearchProblem (thresholdPoly k)
        (TreeMCSPSearchWitnessEncoding.ofCodec (treeCircuitWitnessCodec (thresholdPoly k))))
        (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) r)}
    (hpr : contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w)=true) (hn : 3 ≤ pr.2.n) :
    let B := FixedRawLengthFence.allocation (pairLength a m)
    ∃ z, 2 ≤ z ∧ FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z ∧
      (pr.2.n < FixedRawLengthFence.capacity a m z →
        ∃ T, T ≤ FixedRawLengthFence.countdownDeadline (pairLength a m) ∧
          ∀ r, r < 2^pr.2.n →
            let e := rawMachine.run (T+pr.2.n+2+iterClock (List.replicate pr.2.n false) r)
              (initialConfig rawMachine B (encodePair x w))
            e.state=FixedRawLengthFence.prefixed.seqRight machine (q 2) ∧
            e.head.val=a+m+2+z+pr.2.n+1 ∧
            Target.Span e.tape (a+m+2+z) (iterBits (List.replicate pr.2.n false) r) ∧
            ∀ (i : Fin (tapeLength (pairLength a m) B)) (_lo : 8+2*z+1 ≤ i.val) (hi : i.val < a+m),
              e.tape i=some (Fin.append x w ⟨i.val,hi⟩)) := by
  obtain ⟨_,z,hz,hg,start⟩ := raw_counter_parsed k x w hpr htag hn
  refine ⟨z,hz,hg,?_⟩
  intro hcap
  obtain ⟨T,hR,hT,span,frame,runall⟩ := start hcap
  refine ⟨T,hT,?_⟩
  intro r hbound
  let B := FixedRawLengthFence.allocation (pairLength a m)
  let L := a+m+2+z
  let n := pr.2.n
  let source := FixedRawLengthFence.countdownTape B x w z 0 n
  let ready : Config machine.stateCount (pairLength a m) B :=
    ⟨q 2,⟨L+n+1,hR⟩,installedTape source L n⟩
  have good : Good (List.replicate n false) r :=
    good_of_lt _ _ (by simpa [zero_value] using hbound)
  have hp : L+(List.replicate n false).length+1 < tapeLength (pairLength a m) B := by
    simpa only [List.length_replicate] using hR
  have result := repeated_exact L (List.replicate n false) r ready hp rfl
    (by simp [ready]) span good
  dsimp only
  rw [runall]
  refine ⟨congrArg (FixedRawLengthFence.prefixed.seqRight machine) result.1,
    by simpa only [List.length_replicate] using result.2.1,result.2.2.1,?_⟩
  intro i lo hi
  have low : i.val ≤ L := by dsimp [L]; omega
  change (machine.run (iterClock (List.replicate n false) r) ready).tape i = some (Fin.append x w ⟨i.val,hi⟩)
  rw [result.2.2.2 i (Or.inl low),frame i (Or.inl low)]
  exact raw_source_after_header x w hg (FixedRawLengthFence.resource_bounds (pairLength a m)).1
    (Nat.le_of_lt hcap) i lo hi
end Body
