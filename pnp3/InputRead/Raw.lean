import InputRead.Proof
import AcceptedBody.Closure
namespace InputRead
open Pnp3.Complexity.Uniform.V1
open Pnp4.Frontier.ContractExpansion Pnp4.Frontier Pnp4.AlgorithmsToLowerBounds PairEncoding
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

theorem seed_path (T : Nat → Option Bool) (h n : Nat)
    (marks : ∀ i, h ≤ i → i < h+n → T i=some true) (endBlank : T (h+n)=none) :
    Path (h+n) (n+1) ⟨q 1,h,T⟩ ⟨q 2,h+n,Body.clear T h n⟩ := by
  induction n generalizing T h with
  | zero =>
    have one := hop (q 1) (q 2) h h T none .stay (P := h) le_rfl le_rfl
      (by rw [show T h=none by simpa using endBlank]; rfl) rfl
    have hb : T h=none := by simpa using endBlank
    rw [← hb,put_same] at one
    have hz : Body.clear T h 0=T := by funext i; simp [Body.clear]
    simpa [hz] using one
  | succ n ih =>
    have hb := marks h le_rfl (by omega)
    let U := put T h (some false)
    have one := hop (q 1) (q 1) h (h+1) T (some false) .right (P := h+(n+1))
      (by omega) (by omega) (by rw [hb]; rfl) rfl
    have rest := ih U (h+1)
      (by intro i h1 h2; dsimp [U]; rw [put,if_neg (by omega)]; exact marks i (by omega) (by omega))
      (by dsimp [U]; rw [put,if_neg (by omega)]; simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using endBlank)
    have eqP : h+1+n=h+(n+1) := by omega
    rw [eqP] at rest
    have clearstep : Body.clear (put T h (some false)) (h+1) n = Body.clear T h (n+1) := Body.clear_step T h n
    simpa only [U,clearstep,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using one.append rest

/-- Installation consumes actual unary marks, without assuming precleared scratch. -/
theorem install_path (T : Nat → Option Bool) (left n : Nat)
    (startBlank : T left=none)
    (marks : ∀ i, left < i → i < left+n+1 → T i=some true)
    (endBlank : T (left+n+1)=none) :
    Path (left+n+1) (n+2) ⟨machine.start,left,T⟩
      ⟨q 2,left+n+1,Body.clear T (left+1) n⟩ := by
  have one := hop machine.start (q 1) left (left+1) T none .right (P := left+n+1)
    (by omega) (by omega) (by rw [startBlank]; rfl) rfl
  rw [← startBlank,put_same] at one
  have rest := seed_path T (left+1) n
    (by intro i h1 h2; exact marks i (by omega) (by omega))
    (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using endBlank)
  have eqP : left+1+n=left+n+1 := by omega
  rw [eqP] at rest
  simpa [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using one.append rest


/-- Initial unary-to-zero installation on this exact reader table. -/
theorem install_exact {N B : Nat} (left n : Nat) (c : Config machine.stateCount N B)
    (hp : left+n+1 < tapeLength N B) (hq : c.state=machine.start) (hh : c.head.val=left)
    (hl : c.tape ⟨left,by omega⟩=none)
    (hr : c.tape ⟨left+n+1,hp⟩=none)
    (marks : ∀ i : Fin (tapeLength N B), left < i.val → i.val < left+n+1 → c.tape i=some true) :
    machine.run (n+2) c = ⟨q 2,⟨left+n+1,hp⟩,Body.installedTape c.tape left n⟩ := by
  let T := Body.extend c.tape
  have hleft : T left=none := by simpa [T,Body.extend,show left < tapeLength N B by omega] using hl
  have hright : T (left+n+1)=none := by simpa [T,Body.extend,hp] using hr
  have path := install_path T left n hleft (by
    intro i h1 h2
    have hi : i < tapeLength N B := by omega
    simpa [T,Body.extend,hi] using marks ⟨i,hi⟩ h1 h2) hright
  have he := path.execute hp
  have hc : embed (N := N) (B := B) ⟨machine.start,left,T⟩ (by change left < tapeLength N B; omega) = c := by
    apply Config.ext_parts hq.symm (Fin.ext hh.symm)
    funext i; exact Body.extend_read c.tape i
  rw [hc] at he
  rw [he]
  apply Config.ext_parts
  · rfl
  · rfl
  funext i
  change Body.clear T (left+1) n i.val = Body.installedTape c.tape left n i
  simp only [Body.clear,Body.installedTape]
  have hi : left+1 ≤ i.val ↔ left < i.val := by omega
  have heq : left+1+n=left+n+1 := by omega
  simp only [hi,heq]
  split_ifs <;> first | rfl | exact Body.extend_read c.tape i

/-- Frozen raw capstone. The gamma support guard is explicit; no full truth-table
support is assumed. EOF may coincide with the first table cursor. -/
theorem raw_cursor_parsed (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    {pr : AcceptedBody.Parsed k}
    (hpr : contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w)=true) (hn : 3 ≤ pr.2.n) :
    let B := FixedRawLengthFence.allocation (pairLength a m)
    ∃ z T, 2 ≤ z ∧ FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z ∧
      T ≤ FixedRawLengthFence.countdownDeadline (pairLength a m) ∧
      (pr.2.n < FixedRawLengthFence.capacity a m z → 9+2*z ≤ a+m →
        ∃ (hR : a+m+2+z+pr.2.n+1 < tapeLength (pairLength a m) B) (mode : Fin 3),
          (mode.val=2 ↔ 9+2*z=a+m) ∧
          (∀ hi : 9+2*z < a+m, result mode=Fin.append x w ⟨9+2*z,hi⟩) ∧
          rawMachine.run (T+pr.2.n+2+readClock pr.2.n z (a+m-(9+2*z)))
            (initialConfig rawMachine B (encodePair x w)) =
          FixedRawLengthFence.prefixed.seqEmbedRight machine
            ⟨ready mode,⟨a+m+2+z+pr.2.n+1,hR⟩,
             fun i => if i.val=9+2*z then none else
               Body.installedTape (FixedRawLengthFence.countdownTape B x w z 0 pr.2.n)
                 (a+m+2+z) pr.2.n i⟩) := by
  dsimp only
  obtain ⟨_hnr,z,C,qp,hS,hz,hg,_hh,_hC,_hfirst,success,_reject⟩ :=
    raw_fenced_countdown_parsed_target k x w hpr htag hn
  by_cases cap : pr.2.n < FixedRawLengthFence.capacity a m z
  · obtain ⟨price,he⟩ := success (Nat.le_of_lt cap)
    obtain ⟨T,hT,first,arrived⟩ := Body.first_accept_whole FixedRawLengthFence.prefixed
      (initialConfig FixedRawLengthFence.prefixed _ (encodePair x w)) _ _ he rfl
    refine ⟨z,T,hz,hg,hT.trans price,?_⟩
    intro _ full
    let B := FixedRawLengthFence.allocation (pairLength a m)
    let S := a+m
    let L := a+m+2+z
    let n := pr.2.n
    let p := 9+2*z
    let tape := FixedRawLengthFence.countdownTape B x w z 0 n
    have resource := (FixedRawLengthFence.resource_bounds (pairLength a m)).1
    have cells := FixedRawLengthFence.countdown_success_cells x w hg resource (Nat.le_of_lt cap)
    have geo : a+m+3+z+FixedRawLengthFence.capacity a m z=FixedRawLengthFence.fencePos (pairLength a m) := by
      simp only [FixedRawLengthFence.capacity,FixedRawLengthFence.fencePos,pairLength] at *; omega
    have hR : L+n+1 < tapeLength (pairLength a m) B := by
      have hf : FixedRawLengthFence.fencePos (pairLength a m) < tapeLength (pairLength a m) B := by
        change 3*pairLength a m+2 < pairLength a m+B+1
        change 2*pairLength a m+2 ≤ B at resource
        omega
      dsimp [L,n]; omega
    let entry : Config machine.stateCount (pairLength a m) B := ⟨machine.start,⟨L,hS⟩,tape⟩
    have hl : entry.tape ⟨L,by omega⟩=none := cells.2.2.1 _ rfl
    have hr : entry.tape ⟨L+n+1,hR⟩=none := cells.2.2.2.2.1 _ (by dsimp [L,n]; omega) (by dsimp [L,n]; omega)
    have marks : ∀ i : Fin (tapeLength (pairLength a m) B), L < i.val → i.val < L+n+1 → entry.tape i=some true := by
      intro i h1 h2; exact cells.2.2.2.1 i (by dsimp [L] at h1; omega) (by dsimp [L,n] at h2; omega)
    have install := install_exact L n entry hR rfl rfl hl hr marks
    let start : Config machine.stateCount (pairLength a m) B :=
      ⟨q 2,⟨L+n+1,hR⟩,Body.installedTape tape L n⟩
    have frame (i : Fin (tapeLength (pairLength a m) B)) (hi : i.val ≤ L) : start.tape i=tape i := by
      dsimp [start,Body.installedTape]; rw [if_neg (by omega)]
    have walk : FixedGammaTargetPayloadExhaustion.termWalk (a+m) z=z := by
      unfold FixedGammaTargetPayloadExhaustion.termWalk FixedGammaTargetPayloadLoopFoundation.walk
      omega
    have low (i : Fin (tapeLength (pairLength a m) B)) (hi : i.val < S) :
        start.tape i=FixedGammaTargetPayloadExhaustion.finishTape B x w z i := by
      rw [frame i (by dsimp [L,S] at *; omega)]
      exact cells.1 i hi
    have hp : 2 ≤ p := by dsimp [p]; omega
    have hps : p ≤ S := full
    have fit : S+z+n+3 < tapeLength (pairLength a m) B := by dsimp [S] at *; dsimp [L] at hR; omega
    obtain ⟨mode,hm,hb,retq,reth,rett,_recover⟩ := cursor_exact _ _ p S z n start hp hps fit rfl
      (by dsimp [start,L,S]; omega)
      (by rw [low _ (by dsimp [p,S]; omega)]; unfold FixedGammaTargetPayloadExhaustion.finishTape
          rw [walk,if_pos (by dsimp [p]; omega)])
      (by rw [low _ (by dsimp [p,S]; omega)]; unfold FixedGammaTargetPayloadExhaustion.finishTape
          rw [walk,if_neg (by dsimp [p]; omega),if_pos (by dsimp [p]; omega)])
      (by intro i lo hi; rw [frame i (by dsimp [L,S] at *; omega)]
          exact ⟨_,Body.raw_source_after_header x w hg resource (Nat.le_of_lt cap) i (by dsimp [p] at lo; omega) hi⟩)
      (by rw [frame _ (by dsimp [L,S]; omega)]
          dsimp [tape,FixedRawLengthFence.countdownTape]
          rw [if_neg (by dsimp [S]; omega)]
          simp [FixedGammaTargetUnaryCountdown.loopTape,S])
      (by intro i lo hi; rw [frame i (by dsimp [L]; dsimp [S] at hi; omega)]
          exact cells.2.1 (i.val-S-1) (by omega) i (by omega))
      (by rw [frame _ (by dsimp [L,S]; omega)]; exact cells.2.2.1 _ (by dsimp [L,S]; omega))
      (by intro i lo hi
          refine ⟨false,?_⟩
          change (if L < i.val ∧ i.val < L+n+1 then some false else tape i)=some false
          rw [if_pos (by dsimp [L,S] at *; omega)])
      (by change Body.installedTape tape L n _=none
          rw [Body.installedTape,if_neg (by dsimp [L,S]; omega)]
          exact cells.2.2.2.2.1 _ (by dsimp [S]; omega) (by dsimp [S,n] at *; omega))
    refine ⟨hR,mode,hm,?_,?_⟩
    · intro hi
      have bit := hb hi
      rw [frame _ (by dsimp [L,p]; omega)] at bit
      change FixedRawLengthFence.countdownTape B x w z 0 n _=some (result mode) at bit
      rw [Body.raw_source_after_header x w hg resource (Nat.le_of_lt cap) _ (by change 8+2*z+1 ≤ p; dsimp [p]; omega) hi] at bit
      exact (Option.some.inj bit).symm
    · have re : machine.run (readClock n z (S-p)) start =
          ⟨ready mode,⟨L+n+1,hR⟩,fun i => if i.val=p then none else start.tape i⟩ := by
        apply Config.ext_parts
        · exact retq
        · exact reth
        · funext i; exact rett i
      have hand := FixedRawLengthFence.prefixed.seq_handoff machine
        (initialConfig FixedRawLengthFence.prefixed B (encodePair x w)) first
        (by rw [arrived]) (n+2+readClock n z (S-p))
      rw [arrived] at hand
      rw [machine.run_add,install,re] at hand
      simpa only [entry,start,tape,L,n,B,p,S,Nat.add_assoc] using hand
  · refine ⟨z,0,hz,hg,by simp,?_⟩
    intro h; exact False.elim (cap h)
/-- Bound only for this connected first-read stage, on the original allocation. -/
def stageDeadline (R : Nat) : Nat := 144*(R+1)^2

theorem stage_clock (R n z S p T : Nat) (hn : n ≤ R) (hz : z ≤ R) (hs : S ≤ R)
    (ht : T ≤ 128*(R+1)^2) : T+n+2+readClock n z (S-p) ≤ stageDeadline R := by
  have sub : S-p ≤ R := (Nat.sub_le S p).trans hs
  unfold readClock stageDeadline
  nlinarith

/-- EXACT relation=true discharges parse, tag, target bound and strict capacity.
Only gamma physical support remains an explicit branch guard. -/
theorem accepted_cursor (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (accepted : PartAEndpoint.thresholdContentWitnessRelation k a m x w=true) :
    ∃ pr : AcceptedBody.Parsed k,
      contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr ∧
      Pnp3.Models.Partial.tableLen pr.2.n ≤ a+m ∧
      (3 ≤ pr.2.n → ∃ z T,
        2 ≤ z ∧ FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z ∧
        (9+2*z ≤ a+m →
          ∃ (hR : a+m+2+z+pr.2.n+1 < tapeLength (pairLength a m)
                (FixedRawLengthFence.allocation (pairLength a m))) (mode : Fin 3),
            T+pr.2.n+2+readClock pr.2.n z (a+m-(9+2*z)) ≤ stageDeadline (pairLength a m) ∧
            (mode.val=2 ↔ 9+2*z=a+m) ∧
            (∀ hi : 9+2*z < a+m, result mode=Fin.append x w ⟨9+2*z,hi⟩) ∧
            rawMachine.run (T+pr.2.n+2+readClock pr.2.n z (a+m-(9+2*z)))
              (initialConfig rawMachine (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)) =
            FixedRawLengthFence.prefixed.seqEmbedRight machine
              ⟨ready mode,⟨a+m+2+z+pr.2.n+1,hR⟩,
                fun i => if i.val=9+2*z then none else
                  Body.installedTape (FixedRawLengthFence.countdownTape
                    (FixedRawLengthFence.allocation (pairLength a m)) x w z 0 pr.2.n)
                    (a+m+2+z) pr.2.n i⟩)) := by
  have semantic : contentSemanticAccepts (treeCircuitWitnessCodec (thresholdPoly k))
      (Fin.append x w)=true := by
    have h := accepted
    unfold PartAEndpoint.thresholdContentWitnessRelation PartAEndpoint.contentWitnessRelation at h
    split at h
    · rename_i shape; cases shape
      rwa [AcceptedBody.concat_eq_append] at h
    · contradiction
  have tag : FixedContentTagGate.tagMatches (Fin.append x w)=true := by
    have factor := fixedTag_semantic_factorization.1
      (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)
    rw [semantic] at factor
    simpa using factor.symm
  obtain ⟨pr,hpr,table,_⟩ := AcceptedBody.exact k x w accepted
  refine ⟨pr,hpr,table,?_⟩
  intro hn
  obtain ⟨z,T,hz,hg,ht,run⟩ := raw_cursor_parsed k x w hpr tag hn
  have small : pr.2.n ≤ a+m := by
    have h := Nat.lt_two_pow_self (n := pr.2.n)
    change 2^pr.2.n ≤ a+m at table
    omega
  have cap := AcceptedBody.strict_capacity x w hg small
  refine ⟨z,T,hz,hg,?_⟩
  intro full
  obtain ⟨hR,mode,hm,hb,he⟩ := run cap full
  have pair : a+m ≤ pairLength a m := by simp only [pairLength]; omega
  have zg : z ≤ a+m := by
    have g := ((FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 z hg).1
    omega
  exact ⟨hR,mode,stage_clock _ _ _ _ _ _ (small.trans pair) (zg.trans pair) pair ht,hm,hb,he⟩

end InputRead
