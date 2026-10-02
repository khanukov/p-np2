import Complexity.Uniform.V1.FixedRawLengthFenceContent

/-!
G3s Infrastructure, concrete part only. One fixed raw pair executes the existing
256-state table through installation, H1-H17 and 38 fenced countdown rounds.
The next attempted round decrements 24 to 23 before the false fence rejects.
Every endpoint is a full configuration on raw-length 21 / allocation 45; the
public capstones start from literal initialConfig. Expected tapes never install
runtime data. The payload loop is split 31/31/31/12; no computed segment exceeds
91 steps. Existing sequential embeddings retain the merged dispatcher routing.
No parser field, generic fenced suffix, global polynomial deadline, acceptance
equivalence, model conversion or ContentVerifierBridge is established. In
particular, run 4443 at B=45 is not rejection within budget 45. Left clamps remain.
-/
namespace Pnp3.Complexity.Uniform.V1.FixedRawLengthFence
open PairEncoding
set_option maxRecDepth 40000
set_option maxHeartbeats 800000
/-- The query bit of the closed raw witness. -/
def overflowX : Bitstring 1 := ![true]
/-- Physical content suffix: tag remainder, five gamma zeros and six ones. -/
def overflowW : Bitstring 18 :=
  ![false,true,true,false,false,true,false,false,false,false,false,false,true,true,true,true,true,true]
private def fenced (t : Fin (tapeLength 21 45) → Option Bool) :=
  Function.update t ⟨65, by decide⟩ (some false)
private def content := fenced (FixedPairContentMarkerErase.contentTape 45 overflowX overflowW)
private def mk (q : Fin prefixed.stateCount) (h : Fin (tapeLength 21 45))
    (t : Fin (tapeLength 21 45) → Option Bool) : Config prefixed.stateCount 21 45 := ⟨q,h,t⟩
private def h7 := mk ⟨109, by decide⟩ ⟨19, by decide⟩ content
private def h8 := mk ⟨124, by decide⟩ ⟨8, by decide⟩ content
private def h9 := mk ⟨127, by decide⟩ ⟨13, by decide⟩ content
private def h10 := mk ⟨133, by decide⟩ ⟨13, by decide⟩
  (fenced (FixedContentGammaAnchor.markedTape 45 overflowX overflowW))
private def h11 := mk ⟨161, by decide⟩ ⟨6, by decide⟩ content
private def h12 := mk ⟨170, by decide⟩ ⟨13, by decide⟩
  (fenced (FixedGammaTerminatorScratchBootstrap.scratchTape 45 overflowX overflowW))
private def h13 := mk ⟨188, by decide⟩ ⟨7, by decide⟩
  (fenced (FixedGammaTargetFirstPayload.firstPayloadTape 45 overflowX overflowW true))
private def h14 := mk ⟨202, by decide⟩ ⟨7, by decide⟩
  (fenced (FixedGammaTargetSecondPayload.secondPayloadTape 45 overflowX overflowW true true))
private def loop (r : Fin 6) := mk ⟨216, by decide⟩ ⟨13+r.val, by have := r.isLt; simp [tapeLength]; omega⟩
  (fenced (FixedGammaTargetPayloadLoopFoundation.loopTape 45 overflowX overflowW 5 r.val))
private def h16 := mk ⟨238, by decide⟩ ⟨7, by decide⟩
  (fenced (FixedGammaTargetPayloadExhaustion.finishTape 45 overflowX overflowW 5))
private def h17 := mk ⟨245, by decide⟩ ⟨25, by decide⟩
  (fenced (FixedGammaTargetRegisterDecrement.decTape 45 overflowX overflowW 5 0))
/-- Whole expected countdown tape, including the installed false fence. -/
def overflowTape (v r : Nat) : Fin (tapeLength 21 45) → Option Bool := fun i =>
  if i.val = 65 then some false
  else if i.val = 0 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 6 ∨ i.val = 18 then some true
  else if i.val = 1 ∨ i.val = 4 ∨ i.val = 5 ∨ (7 ≤ i.val ∧ i.val ≤ 12) then some false
  else if 20 ≤ i.val ∧ i.val ≤ 25 then some (v.testBit (25 - i.val))
  else if 27 ≤ i.val ∧ i.val < 27 + r then some true else none


private def snapshot {k n B : Nat} (c : Config k n B) :=
  (c.state.val, c.head.val, List.ofFn c.tape)
private theorem config_of_snapshot {k n B : Nat} {c d : Config k n B}
    (h : snapshot c = snapshot d) : c = d :=
  Config.ext_parts (Fin.ext (congrArg Prod.fst h))
    (Fin.ext (congrArg (fun x => x.2.1) h))
    (List.ofFn_injective (congrArg (fun x => x.2.2) h))

private abbrev safe {k : Nat} (c : Config k 21 45) : Prop :=
  c.head.val ≤ 65 ∧ c.tape ⟨65, by decide⟩ = some false

private theorem trace_add {M : UniformTM} {c d : Config M.stateCount 21 45} {T U : Nat}
    (he : M.run T c = d) (hp : ∀ t, t ≤ T → safe (M.run t c))
    (hs : ∀ t, t ≤ U → safe (M.run t d)) :
    ∀ t, t ≤ T+U → safe (M.run t c) := by
  intro t ht
  by_cases h : t ≤ T
  · exact hp t h
  · rw [show t = T+(t-T) by omega, M.run_add, he]
    exact hs (t-T) (by omega)

-- Concrete G3q suffix computations transported into the unchanged prefixed table.
private theorem h8_exact : prefixed.run 64 h7 = h8 := by
  have h : G.run (n := 21) (budget := 45) 64 ⟨⟨61,by decide⟩,h7.head,h7.tape⟩ =
      ⟨⟨76,by decide⟩,h8.head,h8.tape⟩ := config_of_snapshot (by decide)
  change (machine.seq G).run 64
    (machine.seqEmbedRight G ⟨⟨61,by decide⟩,h7.head,h7.tape⟩) = h8
  rw [UniformTM.seq_run_right,h]
  rfl
private theorem h8_trace : ∀ t, t ≤ 64 → safe (prefixed.run t h7) := by
  have h : ∀ t : Fin 65, safe (prefixed.run t.val h7) := by decide
  exact fun t ht => h ⟨t, by omega⟩
private theorem h9_exact : prefixed.run 6 h8 = h9 := by
  have h : G.run (n := 21) (budget := 45) 6 ⟨⟨76,by decide⟩,h8.head,h8.tape⟩ =
      ⟨⟨79,by decide⟩,h9.head,h9.tape⟩ := config_of_snapshot (by decide)
  change (machine.seq G).run 6
    (machine.seqEmbedRight G ⟨⟨76,by decide⟩,h8.head,h8.tape⟩) = h9
  rw [UniformTM.seq_run_right,h]
  rfl
private theorem h9_trace : ∀ t, t ≤ 6 → safe (prefixed.run t h8) := by
  have h : ∀ t : Fin 7, safe (prefixed.run t.val h8) := by decide
  exact fun t ht => h ⟨t, by omega⟩
private theorem h10_exact : prefixed.run 15 h9 = h10 := by
  have h : G.run (n := 21) (budget := 45) 15 ⟨⟨79,by decide⟩,h9.head,h9.tape⟩ =
      ⟨⟨85,by decide⟩,h10.head,h10.tape⟩ := config_of_snapshot (by decide)
  change (machine.seq G).run 15
    (machine.seqEmbedRight G ⟨⟨79,by decide⟩,h9.head,h9.tape⟩) = h10
  rw [UniformTM.seq_run_right,h]
  rfl
private theorem h10_trace : ∀ t, t ≤ 15 → safe (prefixed.run t h9) := by
  have h : ∀ t : Fin 16, safe (prefixed.run t.val h9) := by decide
  exact fun t ht => h ⟨t, by omega⟩
private theorem h11_exact : prefixed.run 21 h10 = h11 := by
  have h : G.run (n := 21) (budget := 45) 21 ⟨⟨85,by decide⟩,h10.head,h10.tape⟩ =
      ⟨⟨113,by decide⟩,h11.head,h11.tape⟩ := config_of_snapshot (by decide)
  change (machine.seq G).run 21
    (machine.seqEmbedRight G ⟨⟨85,by decide⟩,h10.head,h10.tape⟩) = h11
  rw [UniformTM.seq_run_right,h]
  rfl
private theorem h11_trace : ∀ t, t ≤ 21 → safe (prefixed.run t h10) := by
  have h : ∀ t : Fin 22, safe (prefixed.run t.val h10) := by decide
  exact fun t ht => h ⟨t, by omega⟩
private theorem h12_exact : prefixed.run 22 h11 = h12 := by
  have h : G.run (n := 21) (budget := 45) 22 ⟨⟨113,by decide⟩,h11.head,h11.tape⟩ =
      ⟨⟨122,by decide⟩,h12.head,h12.tape⟩ := config_of_snapshot (by decide)
  change (machine.seq G).run 22
    (machine.seqEmbedRight G ⟨⟨113,by decide⟩,h11.head,h11.tape⟩) = h12
  rw [UniformTM.seq_run_right,h]
  rfl
private theorem h12_trace : ∀ t, t ≤ 22 → safe (prefixed.run t h11) := by
  have h : ∀ t : Fin 23, safe (prefixed.run t.val h11) := by decide
  exact fun t ht => h ⟨t, by omega⟩
private theorem h13_exact : prefixed.run 37 h12 = h13 := by
  have h : G.run (n := 21) (budget := 45) 37 ⟨⟨122,by decide⟩,h12.head,h12.tape⟩ =
      ⟨⟨140,by decide⟩,h13.head,h13.tape⟩ := config_of_snapshot (by decide)
  change (machine.seq G).run 37
    (machine.seqEmbedRight G ⟨⟨122,by decide⟩,h12.head,h12.tape⟩) = h13
  rw [UniformTM.seq_run_right,h]
  rfl
private theorem h13_trace : ∀ t, t ≤ 37 → safe (prefixed.run t h12) := by
  have h : ∀ t : Fin 38, safe (prefixed.run t.val h12) := by decide
  exact fun t ht => h ⟨t, by omega⟩
private theorem h14_exact : prefixed.run 31 h13 = h14 := by
  have h : G.run (n := 21) (budget := 45) 31 ⟨⟨140,by decide⟩,h13.head,h13.tape⟩ =
      ⟨⟨154,by decide⟩,h14.head,h14.tape⟩ := config_of_snapshot (by decide)
  change (machine.seq G).run 31
    (machine.seqEmbedRight G ⟨⟨140,by decide⟩,h13.head,h13.tape⟩) = h14
  rw [UniformTM.seq_run_right,h]
  rfl
private theorem h14_trace : ∀ t, t ≤ 31 → safe (prefixed.run t h13) := by
  have h : ∀ t : Fin 32, safe (prefixed.run t.val h13) := by decide
  exact fun t ht => h ⟨t, by omega⟩
private theorem h15_exact : prefixed.run 12 h14 = (loop 2) := by
  have h : G.run (n := 21) (budget := 45) 12 ⟨⟨154,by decide⟩,h14.head,h14.tape⟩ =
      ⟨⟨168,by decide⟩,(loop 2).head,(loop 2).tape⟩ := config_of_snapshot (by decide)
  change (machine.seq G).run 12
    (machine.seqEmbedRight G ⟨⟨154,by decide⟩,h14.head,h14.tape⟩) = (loop 2)
  rw [UniformTM.seq_run_right,h]
  rfl
private theorem h15_trace : ∀ t, t ≤ 12 → safe (prefixed.run t h14) := by
  have h : ∀ t : Fin 13, safe (prefixed.run t.val h14) := by decide
  exact fun t ht => h ⟨t, by omega⟩
private theorem loop3_exact : prefixed.run 31 (loop 2) = (loop 3) := by
  have h : G.run (n := 21) (budget := 45) 31 ⟨⟨168,by decide⟩,(loop 2).head,(loop 2).tape⟩ =
      ⟨⟨168,by decide⟩,(loop 3).head,(loop 3).tape⟩ := config_of_snapshot (by decide)
  change (machine.seq G).run 31
    (machine.seqEmbedRight G ⟨⟨168,by decide⟩,(loop 2).head,(loop 2).tape⟩) = (loop 3)
  rw [UniformTM.seq_run_right,h]
  rfl
private theorem loop3_trace : ∀ t, t ≤ 31 → safe (prefixed.run t (loop 2)) := by
  have h : ∀ t : Fin 32, safe (prefixed.run t.val (loop 2)) := by decide
  exact fun t ht => h ⟨t, by omega⟩
private theorem loop4_exact : prefixed.run 31 (loop 3) = (loop 4) := by
  have h : G.run (n := 21) (budget := 45) 31 ⟨⟨168,by decide⟩,(loop 3).head,(loop 3).tape⟩ =
      ⟨⟨168,by decide⟩,(loop 4).head,(loop 4).tape⟩ := config_of_snapshot (by decide)
  change (machine.seq G).run 31
    (machine.seqEmbedRight G ⟨⟨168,by decide⟩,(loop 3).head,(loop 3).tape⟩) = (loop 4)
  rw [UniformTM.seq_run_right,h]
  rfl
private theorem loop4_trace : ∀ t, t ≤ 31 → safe (prefixed.run t (loop 3)) := by
  have h : ∀ t : Fin 32, safe (prefixed.run t.val (loop 3)) := by decide
  exact fun t ht => h ⟨t, by omega⟩
private theorem loop5_exact : prefixed.run 31 (loop 4) = (loop 5) := by
  have h : G.run (n := 21) (budget := 45) 31 ⟨⟨168,by decide⟩,(loop 4).head,(loop 4).tape⟩ =
      ⟨⟨168,by decide⟩,(loop 5).head,(loop 5).tape⟩ := config_of_snapshot (by decide)
  change (machine.seq G).run 31
    (machine.seqEmbedRight G ⟨⟨168,by decide⟩,(loop 4).head,(loop 4).tape⟩) = (loop 5)
  rw [UniformTM.seq_run_right,h]
  rfl
private theorem loop5_trace : ∀ t, t ≤ 31 → safe (prefixed.run t (loop 4)) := by
  have h : ∀ t : Fin 32, safe (prefixed.run t.val (loop 4)) := by decide
  exact fun t ht => h ⟨t, by omega⟩
private theorem h16_exact : prefixed.run 12 (loop 5) = h16 := by
  have h : G.run (n := 21) (budget := 45) 12 ⟨⟨168,by decide⟩,(loop 5).head,(loop 5).tape⟩ =
      ⟨⟨190,by decide⟩,h16.head,h16.tape⟩ := config_of_snapshot (by decide)
  change (machine.seq G).run 12
    (machine.seqEmbedRight G ⟨⟨168,by decide⟩,(loop 5).head,(loop 5).tape⟩) = h16
  rw [UniformTM.seq_run_right,h]
  rfl
private theorem h16_trace : ∀ t, t ≤ 12 → safe (prefixed.run t (loop 5)) := by
  have h : ∀ t : Fin 13, safe (prefixed.run t.val (loop 5)) := by decide
  exact fun t ht => h ⟨t, by omega⟩
private theorem h17_exact : prefixed.run 21 h16 = h17 := by
  have h : G.run (n := 21) (budget := 45) 21 ⟨⟨190,by decide⟩,h16.head,h16.tape⟩ =
      ⟨⟨197,by decide⟩,h17.head,h17.tape⟩ := config_of_snapshot (by decide)
  change (machine.seq G).run 21
    (machine.seqEmbedRight G ⟨⟨190,by decide⟩,h16.head,h16.tape⟩) = h17
  rw [UniformTM.seq_run_right,h]
  rfl
private theorem h17_trace : ∀ t, t ≤ 21 → safe (prefixed.run t h16) := by
  have h : ∀ t : Fin 22, safe (prefixed.run t.val h16) := by decide
  exact fun t ht => h ⟨t, by omega⟩

private theorem suffix_exact : prefixed.run 334 h7 = h17 := by
  change prefixed.run (64 + (6 + (15 + (21 + (22 + (37 + (31 + (12 + (31 + (31 + (31 + (12 + (21))))))))))))) h7 = h17
  rw [UniformTM.run_add, h8_exact, UniformTM.run_add, h9_exact, UniformTM.run_add, h10_exact, UniformTM.run_add, h11_exact, UniformTM.run_add, h12_exact, UniformTM.run_add, h13_exact, UniformTM.run_add, h14_exact, UniformTM.run_add, h15_exact, UniformTM.run_add, loop3_exact, UniformTM.run_add, loop4_exact, UniformTM.run_add, loop5_exact, UniformTM.run_add, h16_exact, h17_exact]

private theorem suffix_trace : ∀ t, t ≤ 334 → safe (prefixed.run t h7) := by
  have h16_tail := trace_add h16_exact h16_trace h17_trace
  have loop5_tail := trace_add loop5_exact loop5_trace h16_tail
  have loop4_tail := trace_add loop4_exact loop4_trace loop5_tail
  have loop3_tail := trace_add loop3_exact loop3_trace loop4_tail
  have h15_tail := trace_add h15_exact h15_trace loop3_tail
  have h14_tail := trace_add h14_exact h14_trace h15_tail
  have h13_tail := trace_add h13_exact h13_trace h14_tail
  have h12_tail := trace_add h12_exact h12_trace h13_tail
  have h11_tail := trace_add h11_exact h11_trace h12_tail
  have h10_tail := trace_add h10_exact h10_trace h11_tail
  have h9_tail := trace_add h9_exact h9_trace h10_tail
  have h8_tail := trace_add h8_exact h8_trace h9_tail
  exact h8_tail

/-- Actual tag, width, dispatcher branch and decremented digits of this word. -/
theorem overflow_values :
    FixedContentTagGate.tagMatches (Fin.append overflowX overflowW) = true ∧
    FixedContentGammaTerminator.gammaZeros? (Fin.append overflowX overflowW) = some 5 ∧
    FixedGammaPayloadDispatcherFirstArrival.StrictFirstTerminalAt
      45 overflowX overflowW 21 FixedGammaPayloadDispatcher.qHasOne ∧
    FixedGammaTargetRegisterDecrement.borrow overflowX overflowW 5 = 0 ∧
    (∀ j, j ≤ 5 → (62 : Nat).testBit (5-j) =
      FixedGammaTargetRegisterDecrement.decBit overflowX overflowW 5 0 j) ∧
    (∀ b, 5 < b → (62 : Nat).testBit b = false) := by
  refine ⟨by decide, by decide, ?_, by decide, ?_, ?_⟩
  · exact (FixedGammaPayloadDispatcherFirstArrival.first_true_strict_first_terminal (B := 45) (zeros := 5)
      overflowX overflowW (by decide) (by decide) (by decide) (by decide) (by decide)).1
  · intro j hj; interval_cases j <;> decide
  · intro b hb
    apply Nat.testBit_lt_two_pow
    have h := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show 6 ≤ b by omega)
    omega

private theorem raw_h7 : prefixed.run 2001
    (initialConfig prefixed 45 (encodePair overflowX overflowW)) = h7 := by
  have h := raw_fenced_content_exact (B := 45) overflowX overflowW (by decide)
  change prefixed.run 2001 _ = _ at h
  rw [h]
  apply config_of_snapshot
  decide

/-- Closed raw execution through H17: copied 63, decremented to 62. -/
theorem overflow_h17_exact : prefixed.run 2335
    (initialConfig prefixed 45 (encodePair overflowX overflowW)) =
      ⟨⟨245, by decide⟩, ⟨25, by decide⟩, overflowTape 62 0⟩ := by
  rw [show 2335 = 2001+334 by decide, prefixed.run_add, raw_h7, suffix_exact]
  apply config_of_snapshot
  decide

private def countdownLoop (v r : Nat) : Config FixedGammaTargetUnaryCountdown.stateCount 21 45 :=
  ⟨FixedGammaTargetUnaryCountdown.qLoop, ⟨26, by decide⟩, overflowTape v r⟩

private theorem overflow_round_exact (r : Fin 38) :
    FixedGammaTargetUnaryCountdown.machine.run
      (FixedGammaTargetUnaryCountdown.roundClock 5 r.val) (countdownLoop (62-r.val) r.val) =
        countdownLoop (62-(r.val+1)) (r.val+1) := by
  apply config_of_snapshot
  have h : ∀ r : Fin 38, snapshot (FixedGammaTargetUnaryCountdown.machine.run
      (FixedGammaTargetUnaryCountdown.roundClock 5 r.val) (countdownLoop (62-r.val) r.val)) =
        snapshot (countdownLoop (62-(r.val+1)) (r.val+1)) := by decide
  exact h r

private theorem overflow_round_trace (r : Fin 38) :
    ∀ t, t ≤ FixedGammaTargetUnaryCountdown.roundClock 5 r.val →
      let c := FixedGammaTargetUnaryCountdown.machine.run t (countdownLoop (62-r.val) r.val)
      c.head.val < 65 ∧ c.tape ⟨65, by decide⟩ = some false := by
  have h : ∀ r : Fin 38, ∀ t : Fin (FixedGammaTargetUnaryCountdown.roundClock 5 r.val+1),
      let c := FixedGammaTargetUnaryCountdown.machine.run t.val (countdownLoop (62-r.val) r.val)
      c.head.val < 65 ∧ c.tape ⟨65, by decide⟩ = some false := by decide
  exact fun t ht => h r ⟨t,by omega⟩

private theorem rounds (r : Nat) (hr : r ≤ 38) :
    FixedGammaTargetUnaryCountdown.machine.run (r*r+16*r) (countdownLoop 62 0) =
      countdownLoop (62-r) r ∧
    ∀ t, t ≤ r*r+16*r → safe
      (FixedGammaTargetUnaryCountdown.machine.run t (countdownLoop 62 0)) := by
  induction r with
  | zero =>
    refine ⟨rfl, ?_⟩
    intro t ht
    have hz : t = 0 := by omega
    subst t
    decide
  | succ r ih =>
    obtain ⟨he,ht⟩ := ih (by omega)
    have hc : (r+1)*(r+1)+16*(r+1) =
        (r*r+16*r) + FixedGammaTargetUnaryCountdown.roundClock 5 r := by
      unfold FixedGammaTargetUnaryCountdown.roundClock; ring
    rw [hc]
    refine ⟨?_, trace_add he ht ?_⟩
    · rw [UniformTM.run_add,he]
      exact overflow_round_exact ⟨r,by omega⟩
    · intro t hb
      have h := overflow_round_trace ⟨r,by omega⟩ t hb
      exact ⟨Nat.le_of_lt h.1,h.2⟩

private theorem last_scan : FixedGammaTargetUnaryCountdown.machine.run 53 (countdownLoop 24 38) =
    ⟨FixedGammaTargetUnaryCountdown.qRunEnd, ⟨65,by decide⟩, overflowTape 23 38⟩ :=
  config_of_snapshot (by decide)
private theorem last_trace : ∀ t, t ≤ 53 →
    safe (FixedGammaTargetUnaryCountdown.machine.run t (countdownLoop 24 38)) := by
  have h : ∀ t : Fin 54,
      safe (FixedGammaTargetUnaryCountdown.machine.run t.val (countdownLoop 24 38)) := by decide
  exact fun t ht => h ⟨t,by omega⟩

private def countdownEmbed (c : Config FixedGammaTargetUnaryCountdown.stateCount 21 45) :
    Config prefixed.stateCount 21 45 :=
  machine.seqEmbedRight G (
  FixedPairConcatSentinel.machine.seqEmbedRight FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.machine (
  FixedPairSeparatorCursor.machine.seqEmbedRight FixedPairSeparatorHoleTagRemovalShiftAlignmentCountdown.machine (
  FixedPairSeparatorHole.machine.seqEmbedRight FixedPairTagRemovalShiftAlignmentCountdown.machine (
  FixedPairTagRemoval.machine.seqEmbedRight FixedPairOriginShiftAlignmentCountdown.machine (
  FixedPairOriginShiftBootstrap.machine.seqEmbedRight FixedPairOriginAlignmentContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine (
  FixedPairOriginAlignment.machine.seqEmbedRight FixedPairContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine (
  FixedPairContentMarkerErase.machine.seqEmbedRight FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine (
  FixedContentTagGate.machine.seqEmbedRight FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine (
  FixedContentGammaTerminator.machine.seqEmbedRight FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine (
  FixedContentGammaAnchor.machine.seqEmbedRight FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine (
  FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.mergedDispatcher.seqEmbedRight FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine (
  FixedGammaTerminatorScratchBootstrap.machine.seqEmbedRight FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine (
  FixedGammaTargetFirstPayload.machine.seqEmbedRight FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine (
  FixedGammaTargetSecondPayload.machine.seqEmbedRight FixedGammaTargetMarkersLoopDecrementCountdown.machine (
  FixedGammaTargetPayloadLoopFoundation.machine.seqEmbedRight FixedGammaTargetLoopDecrementCountdown.machine (
  FixedGammaTargetPayloadRound.machine.seqEmbedRight FixedGammaTargetDecrementCountdown.machine (
  FixedGammaTargetRegisterDecrement.machine.seqEmbedRight FixedGammaTargetUnaryCountdown.machine c)))))))))))))))))

private theorem countdown_run (t : Nat) (c : Config FixedGammaTargetUnaryCountdown.stateCount 21 45) :
    prefixed.run t (countdownEmbed c) =
      countdownEmbed (FixedGammaTargetUnaryCountdown.machine.run t c) := by
  simp only [countdownEmbed, prefixed,
    FixedPairSentinelCursorHoleTagRemovalShiftAlignmentCountdown.machine,
    FixedPairConcatSentinel.machine,
    FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.machine,
    FixedPairSeparatorCursor.machine,
    FixedPairSeparatorHoleTagRemovalShiftAlignmentCountdown.machine,
    FixedPairSeparatorHole.machine,
    FixedPairTagRemovalShiftAlignmentCountdown.machine,
    FixedPairTagRemoval.machine,
    FixedPairOriginShiftAlignmentCountdown.machine,
    FixedPairOriginShiftBootstrap.machine,
    FixedPairOriginAlignmentContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine,
    FixedPairOriginAlignment.machine,
    FixedPairContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine,
    FixedPairContentMarkerErase.machine,
    FixedContentTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine,
    FixedContentTagGate.machine,
    FixedContentGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine,
    FixedContentGammaTerminator.machine,
    FixedContentGammaAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine,
    FixedContentGammaAnchor.machine,
    FixedGammaPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine,
    FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine,
    FixedGammaTerminatorScratchBootstrap.machine,
    FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine,
    FixedGammaTargetFirstPayload.machine,
    FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine,
    FixedGammaTargetSecondPayload.machine,
    FixedGammaTargetMarkersLoopDecrementCountdown.machine,
    FixedGammaTargetPayloadLoopFoundation.machine,
    FixedGammaTargetLoopDecrementCountdown.machine,
    FixedGammaTargetPayloadRound.machine,
    FixedGammaTargetDecrementCountdown.machine,
    FixedGammaTargetRegisterDecrement.machine,
    UniformTM.seq_run_right]

private theorem countdown_embed_fields (c : Config FixedGammaTargetUnaryCountdown.stateCount 21 45) :
    (countdownEmbed c).state.val = 245+c.state.val ∧
    (countdownEmbed c).head = c.head ∧ (countdownEmbed c).tape = c.tape := by
  refine ⟨?_,rfl,rfl⟩
  change 48+(7+(5+(3+(9+(7+(26+(4+(15+(3+(6+(28+(9+(18+(14+(14+(22+(7+c.state.val))))))))))))))))) = _
  omega

private theorem loop_entry : prefixed.run 2337
    (initialConfig prefixed 45 (encodePair overflowX overflowW)) = countdownEmbed (countdownLoop 62 0) := by
  rw [show 2337 = 2335+2 by decide, prefixed.run_add, overflow_h17_exact]
  apply config_of_snapshot
  decide

/-- The next attempted round has already decremented 24 to 23 at the fence. -/
theorem overflow_prereject_exact : prefixed.run 4442
    (initialConfig prefixed 45 (encodePair overflowX overflowW)) =
      ⟨⟨251,by decide⟩,⟨65,by decide⟩,overflowTape 23 38⟩ := by
  rw [show 4442 = 2337+(2052+53) by decide, prefixed.run_add, loop_entry,
    countdown_run, UniformTM.run_add, (rounds 38 (by decide)).1, last_scan]
  apply Config.ext_parts
  · apply Fin.ext
    exact (countdown_embed_fields _).1
  · rfl
  · rfl

/-- The existing false-symbol reject row, with unchanged symbol and head. -/
theorem overflow_reject_row : prefixed.step ⟨251,by decide⟩ (some false) =
    (prefixed.reject,some false,Move.stay) := by decide

/-- Literal raw-input rejection and full-configuration persistence. -/
theorem overflow_reject_exact (s : Nat) : prefixed.run (4443+s)
    (initialConfig prefixed 45 (encodePair overflowX overflowW)) =
      ⟨prefixed.reject,⟨65,by decide⟩,overflowTape 23 38⟩ := by
  have hr : prefixed.run 4443 (initialConfig prefixed 45 (encodePair overflowX overflowW)) =
      ⟨prefixed.reject,⟨65,by decide⟩,overflowTape 23 38⟩ := by
    rw [show 4443 = 4442+1 by decide, prefixed.run_add, overflow_prereject_exact]
    apply config_of_snapshot
    decide
  rw [prefixed.run_add,hr,prefixed.run_reject _ rfl]


private theorem countdown_entry_trace : ∀ t, t ≤ 2 → safe (prefixed.run t h17) := by
  have h : ∀ t : Fin 3, safe (prefixed.run t.val h17) := by decide
  exact fun t ht => h ⟨t,by omega⟩

private theorem countdown_entry_exact : prefixed.run 2 h17 = countdownEmbed (countdownLoop 62 0) :=
  config_of_snapshot (by decide)

private theorem countdown_safe (t : Nat) (c : Config FixedGammaTargetUnaryCountdown.stateCount 21 45)
    (h : safe (FixedGammaTargetUnaryCountdown.machine.run t c)) :
    safe (prefixed.run t (countdownEmbed c)) := by
  rw [countdown_run]
  exact h

private theorem tail_trace : ∀ t, t ≤ 2108 → safe (prefixed.run t h17) := by
  have hs : ∀ t, t ≤ 54 → safe (FixedGammaTargetUnaryCountdown.machine.run t (countdownLoop 24 38)) := by
    refine trace_add (U := 1) last_scan last_trace ?_
    have h : ∀ t : Fin 2, safe (FixedGammaTargetUnaryCountdown.machine.run t.val
      ⟨FixedGammaTargetUnaryCountdown.qRunEnd, ⟨65,by decide⟩, overflowTape 23 38⟩) := by decide
    exact fun t ht => h ⟨t,by omega⟩
  have hrounds := trace_add (rounds 38 (by decide)).1 (rounds 38 (by decide)).2 hs
  exact trace_add countdown_entry_exact countdown_entry_trace
    (fun t ht => countdown_safe t _ (hrounds t ht))

/-- The installed fence survives from installation through the rejecting step. -/
theorem overflow_fence_trace : ∀ t, t ≤ 2926 →
    let c := prefixed.run (1517+t)
      (initialConfig prefixed 45 (encodePair overflowX overflowW))
    c.head.val ≤ 65 ∧ c.tape ⟨65,by decide⟩ = some false := by
  let c0 := prefixed.run 1517 (initialConfig prefixed 45 (encodePair overflowX overflowW))
  have he : prefixed.run 484 c0 = h7 := by
    rw [← prefixed.run_add]; exact raw_h7
  have hp : ∀ t, t ≤ 484 → safe (prefixed.run t c0) := by
    intro t ht
    have h := raw_fenced_content_trace (B := 45) overflowX overflowW (by decide) t ht
    change safe (prefixed.run t (prefixed.run 1517 _))
    rw [← prefixed.run_add]
    exact ⟨h.1.trans (by decide),h.2.1⟩
  have h := trace_add he hp (trace_add suffix_exact suffix_trace tail_trace)
  intro t ht
  rw [prefixed.run_add]
  exact h t ht

end Pnp3.Complexity.Uniform.V1.FixedRawLengthFence
