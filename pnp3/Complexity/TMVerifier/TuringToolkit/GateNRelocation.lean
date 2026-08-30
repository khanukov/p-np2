import Complexity.TMVerifier.TuringToolkit.GateNTapeState
import Complexity.TMVerifier.TuringToolkit.GateOneScanner

/-!
# GN-3A: generic local G1 relocation

**Progress classification: infrastructure, not P-vs-NP mainline progress.**
This file relocates a bounded piece of a `G1M` configuration into an arbitrary
future machine configuration.  It introduces no GN machine, controller, mode,
copier, clock, execution trace, or acceptance theorem, and reduces neither
pnp4 lower-bound source obligation.

For source input length `W`, the local footprint is exactly the half-open span
`[0, W + 5)`.  It consists of the `W` input cells, the four cells of the
explicit trailing blank frame, and the possible one-cell head landing just
after that frame.  The quadratic tail of `G1M.tapeLength W` is deliberately
not copied.  In particular the last blank frame starts at `W` and satisfies
`W + 4 < W + 5`; the smaller bound `W + 4` cannot state that fact.

All target-machine results retain the explicit physical-room hypothesis
`base + (W + 5) <= M.tapeLength N`.  GN-2's word inequality `W + 16 <= N`
implies the base-zero instance for a `G1M` target, but is not silently treated
as room for an arbitrary machine.  A future `GNM` will separately need its
own clock proof (in particular the intended `N <= clock N` comparison); no
such machine or clock is defined here.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

open Pnp3.Internal.PsubsetPpoly.TM.FrameScan

universe u

/-! ## Exact local footprint and indices -/

/-- The GN-3A local G1 footprint. -/
def gnLocalSpan (W : Nat) : Nat := W + 5

/-- Every local-footprint cell exists on the source `G1M` tape. -/
theorem gnLocalSpan_le_g1_tapeLength (W : Nat) :
    gnLocalSpan W <= G1M.tapeLength W := by
  change W + 5 <= W + g1Clock W + 1
  have hclock : 4 <= g1Clock W := by
    unfold g1Clock
    omega
  omega

/-- The final four-cell blank frame fits in the `W + 5` footprint. -/
theorem gnLocalSpan_final_frame_fits (W : Nat) : W + 4 < gnLocalSpan W := by
  simp [gnLocalSpan]

/-- `W + 4` is not enough to express that the final frame starting at `W`
fits under the strict physical-frame convention. -/
theorem gnLocalSpan_four_insufficient (W : Nat) : ¬ (W + 4 < W + 4) := by
  omega

/-- Exact arithmetic characterization of target room for the last local
frame, including its one-cell post-frame landing. -/
theorem gnLocalSpan_room_iff {M : TM.{u}} {N base W : Nat} :
    base + W + 4 < M.tapeLength N <->
      base + gnLocalSpan W <= M.tapeLength N := by
  simp [gnLocalSpan]
  omega

/-- A local offset as an index of the source G1 tape. -/
def gnSourceIndex (W j : Nat) (hj : j < gnLocalSpan W) :
    Fin (G1M.tapeLength W) :=
  ⟨j, lt_of_lt_of_le hj (gnLocalSpan_le_g1_tapeLength W)⟩

/-- A local offset shifted to the target tape. -/
def gnTargetIndex (M : TM.{u}) (N base W j : Nat)
    (hroom : base + gnLocalSpan W <= M.tapeLength N)
    (hj : j < gnLocalSpan W) : Fin (M.tapeLength N) :=
  ⟨base + j, by omega⟩

@[simp] theorem gnSourceIndex_val (W j : Nat) (hj : j < gnLocalSpan W) :
    (gnSourceIndex W j hj : Nat) = j := rfl

@[simp] theorem gnTargetIndex_val {M : TM.{u}} (N base W j : Nat)
    (hroom : base + gnLocalSpan W <= M.tapeLength N)
    (hj : j < gnLocalSpan W) :
    (gnTargetIndex M N base W j hroom hj : Nat) = base + j := rfl

/-! ## Local overlay and shifted configurations -/

/-- Overlay exactly source offsets `[0, W + 5)` at `base`; preserve the
caller's ambient target tape everywhere else. -/
def gnOverlayTape (M : TM.{u}) {W N : Nat} (base : Nat)
    (_hroom : base + gnLocalSpan W <= M.tapeLength N)
    (c : Configuration (M := G1M) W)
    (ambient : Fin (M.tapeLength N) -> Bool) : Fin (M.tapeLength N) -> Bool :=
  fun i =>
    if h : base <= (i : Nat) ∧ (i : Nat) < base + gnLocalSpan W then
      c.tape (gnSourceIndex W ((i : Nat) - base) (by omega))
    else ambient i

/-- Shift source control/head/local tape into an arbitrary target machine.
The state map is merely an injection parameter here; injectivity is needed
only by projections that recover source-state equality. -/
def gnShiftConfig (M : TM.{u}) {W N : Nat} (base : Nat)
    (ι : G1M.state -> M.state)
    (ambient : Fin (M.tapeLength N) -> Bool)
    (c : Configuration (M := G1M) W)
    (hroom : base + gnLocalSpan W <= M.tapeLength N)
    (hhead : (c.head : Nat) < gnLocalSpan W) : Configuration (M := M) N where
  state := ι c.state
  head := gnTargetIndex M N base W c.head hroom hhead
  tape := gnOverlayTape M base hroom c ambient

@[simp] theorem gnOverlayTape_inside {M : TM.{u}} {W N base j : Nat}
    (hroom : base + gnLocalSpan W <= M.tapeLength N)
    (c : Configuration (M := G1M) W)
    (ambient : Fin (M.tapeLength N) -> Bool) (hj : j < gnLocalSpan W) :
    gnOverlayTape M base hroom c ambient
        (gnTargetIndex M N base W j hroom hj) =
      c.tape (gnSourceIndex W j hj) := by
  unfold gnOverlayTape
  simp only [gnTargetIndex_val]
  rw [dif_pos (show base <= base + j ∧
    base + j < base + gnLocalSpan W by omega)]
  congr 1
  apply Fin.ext
  simp

@[simp] theorem gnOverlayTape_outside {M : TM.{u}} {W N base : Nat}
    (hroom : base + gnLocalSpan W <= M.tapeLength N)
    (c : Configuration (M := G1M) W)
    (ambient : Fin (M.tapeLength N) -> Bool)
    (i : Fin (M.tapeLength N))
    (hout : (i : Nat) < base ∨ base + gnLocalSpan W <= (i : Nat)) :
    gnOverlayTape M base hroom c ambient i = ambient i := by
  unfold gnOverlayTape
  rw [dif_neg (show ¬ (base <= (i : Nat) ∧
    (i : Nat) < base + gnLocalSpan W) by omega)]

@[simp] theorem gnShiftConfig_state {M : TM.{u}} {W N base : Nat}
    (ι : G1M.state -> M.state) (ambient : Fin (M.tapeLength N) -> Bool)
    (c : Configuration (M := G1M) W)
    (hroom : base + gnLocalSpan W <= M.tapeLength N)
    (hhead : (c.head : Nat) < gnLocalSpan W) :
    (gnShiftConfig M base ι ambient c hroom hhead).state = ι c.state := rfl

/-- An injective state map reflects source-state equality through the shifted
state projection. -/
theorem gnShiftConfig_state_eq_iff {M : TM.{u}} {W N base : Nat}
    (ι : G1M.state -> M.state) (hι : Function.Injective ι)
    (ambient : Fin (M.tapeLength N) -> Bool)
    (c d : Configuration (M := G1M) W)
    (hroom : base + gnLocalSpan W <= M.tapeLength N)
    (hc : (c.head : Nat) < gnLocalSpan W)
    (hd : (d.head : Nat) < gnLocalSpan W) :
    (gnShiftConfig M base ι ambient c hroom hc).state =
        (gnShiftConfig M base ι ambient d hroom hd).state <->
      c.state = d.state := by
  simp only [gnShiftConfig_state]
  exact ⟨fun h => hι h, congrArg ι⟩

@[simp] theorem gnShiftConfig_head_val {M : TM.{u}} {W N base : Nat}
    (ι : G1M.state -> M.state) (ambient : Fin (M.tapeLength N) -> Bool)
    (c : Configuration (M := G1M) W)
    (hroom : base + gnLocalSpan W <= M.tapeLength N)
    (hhead : (c.head : Nat) < gnLocalSpan W) :
    ((gnShiftConfig M base ι ambient c hroom hhead).head : Nat) =
      base + (c.head : Nat) := rfl

@[simp] theorem gnShiftConfig_bit_inside {M : TM.{u}} {W N base j : Nat}
    (ι : G1M.state -> M.state) (ambient : Fin (M.tapeLength N) -> Bool)
    (c : Configuration (M := G1M) W)
    (hroom : base + gnLocalSpan W <= M.tapeLength N)
    (hhead : (c.head : Nat) < gnLocalSpan W) (hj : j < gnLocalSpan W) :
    (gnShiftConfig M base ι ambient c hroom hhead).tape
        (gnTargetIndex M N base W j hroom hj) =
      c.tape (gnSourceIndex W j hj) := by
  exact gnOverlayTape_inside hroom c ambient hj

@[simp] theorem gnShiftConfig_bit_outside {M : TM.{u}} {W N base : Nat}
    (ι : G1M.state -> M.state) (ambient : Fin (M.tapeLength N) -> Bool)
    (c : Configuration (M := G1M) W)
    (hroom : base + gnLocalSpan W <= M.tapeLength N)
    (hhead : (c.head : Nat) < gnLocalSpan W)
    (i : Fin (M.tapeLength N))
    (hout : (i : Nat) < base ∨ base + gnLocalSpan W <= (i : Nat)) :
    (gnShiftConfig M base ι ambient c hroom hhead).tape i = ambient i := by
  exact gnOverlayTape_outside hroom c ambient i hout

/-- Every complete four-cell frame inside the local span is copied exactly. -/
theorem gnShiftConfig_frame_inside {M : TM.{u}} {W N base h : Nat}
    (ι : G1M.state -> M.state) (ambient : Fin (M.tapeLength N) -> Bool)
    (c : Configuration (M := G1M) W)
    (hroom : base + gnLocalSpan W <= M.tapeLength N)
    (hhead : (c.head : Nat) < gnLocalSpan W) (hframe : h + 4 < gnLocalSpan W) :
    physicalBitsAt (h := base + h) (by omega)
        (gnShiftConfig M base ι ambient c hroom hhead).tape =
      physicalBitsAt (h := h) (by
        exact lt_of_lt_of_le hframe (gnLocalSpan_le_g1_tapeLength W)) c.tape := by
  have e0 := gnShiftConfig_bit_inside (j := h)
    ι ambient c hroom hhead (by omega)
  have e1 := gnShiftConfig_bit_inside (j := h + 1)
    ι ambient c hroom hhead (by omega)
  have e2 := gnShiftConfig_bit_inside (j := h + 2)
    ι ambient c hroom hhead (by omega)
  have e3 := gnShiftConfig_bit_inside (j := h + 3)
    ι ambient c hroom hhead (by omega)
  simp only [physicalBitsAt, List.cons.injEq]
  constructor
  · simpa only [Nat.add_assoc] using e0
  constructor
  · simpa only [Nat.add_assoc] using e1
  constructor
  · simpa only [Nat.add_assoc] using e2
  constructor
  · simpa only [Nat.add_assoc] using e3
  trivial

/-- Extensionality of local overlays: local source agreement and outside
ambient agreement determine the whole target tape. -/
theorem gnOverlayTape_ext {M : TM.{u}} {W N base : Nat}
    (hroom : base + gnLocalSpan W <= M.tapeLength N)
    {c d : Configuration (M := G1M) W}
    {ambient ambient' : Fin (M.tapeLength N) -> Bool}
    (hlocal : forall j (hj : j < gnLocalSpan W),
      c.tape (gnSourceIndex W j hj) = d.tape (gnSourceIndex W j hj))
    (houtside : forall i : Fin (M.tapeLength N),
      ((i : Nat) < base ∨ base + gnLocalSpan W <= (i : Nat)) ->
        ambient i = ambient' i) :
    gnOverlayTape M base hroom c ambient =
      gnOverlayTape M base hroom d ambient' := by
  funext i
  by_cases hi : base <= (i : Nat) ∧ (i : Nat) < base + gnLocalSpan W
  · simp only [gnOverlayTape, dif_pos hi]
    exact hlocal ((i : Nat) - base) (by omega)
  · simp only [gnOverlayTape, dif_neg hi]
    exact houtside i (by omega)

/-- Componentwise extensionality specialized to shifted configurations. -/
theorem gnShiftConfig_ext {M : TM.{u}} {W N base : Nat}
    (ι : G1M.state -> M.state)
    {ambient ambient' : Fin (M.tapeLength N) -> Bool}
    {c d : Configuration (M := G1M) W}
    (hroom : base + gnLocalSpan W <= M.tapeLength N)
    (hc : (c.head : Nat) < gnLocalSpan W)
    (hd : (d.head : Nat) < gnLocalSpan W)
    (hstate : ι c.state = ι d.state) (hhead : c.head = d.head)
    (hlocal : forall j (hj : j < gnLocalSpan W),
      c.tape (gnSourceIndex W j hj) = d.tape (gnSourceIndex W j hj))
    (houtside : forall i : Fin (M.tapeLength N),
      ((i : Nat) < base ∨ base + gnLocalSpan W <= (i : Nat)) ->
        ambient i = ambient' i) :
    gnShiftConfig M base ι ambient c hroom hc =
      gnShiftConfig M base ι ambient' d hroom hd := by
  apply Configuration.ext_of_components hstate
  · apply Fin.ext
    simp [hhead]
  · exact gnOverlayTape_ext hroom hlocal houtside

/-! ## Local safety and transition-tuple delegation -/

/-- One source step stays strictly within the local footprint and does not
use the source tape's left clamp.  Both movement clauses are conditional on
the actual transition tuple, so stationary steps remain admissible. -/
def G1LocalStepSafe {W : Nat} (c : Configuration (M := G1M) W) : Prop :=
  (c.head : Nat) < gnLocalSpan W ∧
    (((G1M.step c.state (c.tape c.head)).snd.snd = Move.left) ->
      0 < (c.head : Nat)) ∧
    (((G1M.step c.state (c.tape c.head)).snd.snd = Move.right) ->
      (c.head : Nat) + 1 < gnLocalSpan W)

/-- Delegation is only equality of the transition tuple.  It does not assume
or package an equality of `stepConfig`s. -/
def G1StepDelegates (M : TM.{u}) (ι : G1M.state -> M.state)
    {W : Nat} (c : Configuration (M := G1M) W) : Prop :=
  M.step (ι c.state) (c.tape c.head) =
    (ι (G1M.step c.state (c.tape c.head)).fst,
      (G1M.step c.state (c.tape c.head)).snd.fst,
      (G1M.step c.state (c.tape c.head)).snd.snd)

/-- Local safety derives the next source head's membership in `[0,W+5)`. -/
theorem gn_local_step_safe_next_head {W : Nat}
    (c : Configuration (M := G1M) W) (hsafe : G1LocalStepSafe c) :
    ((TM.stepConfig (M := G1M) c).head : Nat) < gnLocalSpan W := by
  rcases hsafe with ⟨hhead, hleft, hright⟩
  rw [stepConfig_head]
  generalize hm : (G1M.step c.state (c.tape c.head)).snd.snd = move
  cases move with
  | stay => simpa using hhead
  | left =>
      rw [Configuration.moveHead_left_val_of_pos c (hleft hm)]
      omega
  | right =>
      have hsource : (c.head : Nat) + 1 < G1M.tapeLength W :=
        lt_of_lt_of_le (hright hm) (gnLocalSpan_le_g1_tapeLength W)
      rw [Configuration.moveHead_right_lt c hsource]
      exact hright hm

/-- Under local safety, moving the shifted target head commutes exactly with
moving the source head and then shifting. -/
theorem gn_shift_moveHead_val {M : TM.{u}} {W N base : Nat}
    (ι : G1M.state -> M.state) (ambient : Fin (M.tapeLength N) -> Bool)
    (c : Configuration (M := G1M) W)
    (hroom : base + gnLocalSpan W <= M.tapeLength N)
    (hsafe : G1LocalStepSafe c) :
    let move := (G1M.step c.state (c.tape c.head)).snd.snd
    ((Configuration.moveHead
        (c := gnShiftConfig M base ι ambient c hroom hsafe.1) move :
          Fin (M.tapeLength N)) : Nat) =
      base + ((Configuration.moveHead (c := c) move :
        Fin (G1M.tapeLength W)) : Nat) := by
  dsimp only
  rcases hsafe with ⟨hhead, hleft, hright⟩
  generalize hm : (G1M.step c.state (c.tape c.head)).snd.snd = move at hleft hright ⊢
  cases move with
  | stay => simp
  | left =>
      have hpos : 0 < (c.head : Nat) := hleft rfl
      have htpos : 0 < ((gnShiftConfig M base ι ambient c hroom hhead).head : Nat) := by
        simp
        omega
      rw [Configuration.moveHead_left_val_of_pos _ htpos,
        Configuration.moveHead_left_val_of_pos c hpos]
      simp
      omega
  | right =>
      have hnext : (c.head : Nat) + 1 < gnLocalSpan W := hright rfl
      have hs : (c.head : Nat) + 1 < G1M.tapeLength W :=
        lt_of_lt_of_le hnext (gnLocalSpan_le_g1_tapeLength W)
      have ht : ((gnShiftConfig M base ι ambient c hroom hhead).head : Nat) + 1 <
          M.tapeLength N := by
        simp only [gnShiftConfig_head_val]
        omega
      rw [Configuration.moveHead_right_lt _ ht,
        Configuration.moveHead_right_lt c hs]
      rfl

/-- Writing one delegated local cell commutes with overlaying the complete
post-step source tape; this is the full-tape part of one-step conjugacy. -/
theorem gn_shift_write_tape {M : TM.{u}} {W N base : Nat}
    (ι : G1M.state -> M.state) (ambient : Fin (M.tapeLength N) -> Bool)
    (c : Configuration (M := G1M) W)
    (hroom : base + gnLocalSpan W <= M.tapeLength N)
    (hsafe : G1LocalStepSafe c) (b : Bool) :
    (gnShiftConfig M base ι ambient c hroom hsafe.1).write
        (gnShiftConfig M base ι ambient c hroom hsafe.1).head b =
      gnOverlayTape M base hroom
        ({ c with tape := c.write c.head b } : Configuration (M := G1M) W)
        ambient := by
  funext i
  by_cases hi : base <= (i : Nat) ∧ (i : Nat) < base + gnLocalSpan W
  · let j := (i : Nat) - base
    have hj : j < gnLocalSpan W := by dsimp [j]; omega
    have hitarget : gnTargetIndex M N base W j hroom hj = i := by
      apply Fin.ext
      simp [j]
      omega
    rw [← hitarget]
    by_cases hh : j = (c.head : Nat)
    · have hsource : gnSourceIndex W j hj = c.head := by
        apply Fin.ext
        simp [hh]
      have htarget : gnTargetIndex M N base W j hroom hj =
          (gnShiftConfig M base ι ambient c hroom hsafe.1).head := by
        apply Fin.ext
        simp [hh]
      rw [htarget, Configuration.write_self]
      rw [← htarget]
      rw [gnOverlayTape_inside]
      rw [hsource]
      change b = c.write c.head b c.head
      exact (Configuration.write_self c c.head b).symm
    · have hsource : gnSourceIndex W j hj ≠ c.head := by
        intro h
        apply hh
        exact Fin.ext_iff.mp h
      have htarget : gnTargetIndex M N base W j hroom hj ≠
          (gnShiftConfig M base ι ambient c hroom hsafe.1).head := by
        intro h
        apply hh
        have hv := Fin.ext_iff.mp h
        simp [gnShiftConfig, gnTargetIndex, j] at hv
        omega
      rw [Configuration.write_other _ htarget b]
      rw [gnShiftConfig_bit_inside]
      rw [gnOverlayTape_inside]
      exact (Configuration.write_other c hsource b).symm
  · have hout : (i : Nat) < base ∨ base + gnLocalSpan W <= (i : Nat) := by omega
    have htarget : i ≠ (gnShiftConfig M base ι ambient c hroom hsafe.1).head := by
      intro h
      have hv : (i : Nat) = base + (c.head : Nat) := by
        simpa only [gnShiftConfig_head_val] using congrArg Fin.val h
      have hlocal := hsafe.1
      rcases hout with hout | hout <;> omega
    rw [Configuration.write_other _ htarget b]
    rw [gnShiftConfig_bit_outside ι ambient c hroom hsafe.1 i hout]
    exact (gnOverlayTape_outside hroom _ ambient i hout).symm

/-- Exact one-step conjugacy from tuple delegation.  The target step writes
the full shifted post-step tape, and its next-head proof is derived from local
safety rather than supplied by the caller. -/
theorem gn_delegate_step_shift {M : TM.{u}} {W N base : Nat}
    (ι : G1M.state -> M.state) (ambient : Fin (M.tapeLength N) -> Bool)
    (c : Configuration (M := G1M) W)
    (hroom : base + gnLocalSpan W <= M.tapeLength N)
    (hsafe : G1LocalStepSafe c) (hdelegate : G1StepDelegates M ι c) :
    TM.stepConfig (M := M)
        (gnShiftConfig M base ι ambient c hroom hsafe.1) =
      gnShiftConfig M base ι ambient (TM.stepConfig (M := G1M) c) hroom
        (gn_local_step_safe_next_head c hsafe) := by
  apply Configuration.ext_of_components
  · rw [stepConfig_state]
    have hscan :
        (gnShiftConfig M base ι ambient c hroom hsafe.1).tape
            (gnShiftConfig M base ι ambient c hroom hsafe.1).head =
          c.tape c.head :=
      gnShiftConfig_bit_inside ι ambient c hroom hsafe.1 hsafe.1
    simp only [gnShiftConfig_state, hscan]
    exact congrArg Prod.fst hdelegate
  · apply Fin.ext
    rw [stepConfig_head]
    simp only [gnShiftConfig_head_val]
    have hscan :
        (gnShiftConfig M base ι ambient c hroom hsafe.1).tape
            (gnShiftConfig M base ι ambient c hroom hsafe.1).head =
          c.tape c.head := by
      exact gnShiftConfig_bit_inside ι ambient c hroom hsafe.1 hsafe.1
    simp only [gnShiftConfig_state, hscan]
    rw [hdelegate, stepConfig_head]
    exact gn_shift_moveHead_val ι ambient c hroom hsafe
  · rw [stepConfig_tape]
    have hscan :
        (gnShiftConfig M base ι ambient c hroom hsafe.1).tape
            (gnShiftConfig M base ι ambient c hroom hsafe.1).head =
          c.tape c.head :=
      gnShiftConfig_bit_inside ι ambient c hroom hsafe.1 hsafe.1
    simp only [gnShiftConfig_state, hscan]
    rw [hdelegate]
    change (gnShiftConfig M base ι ambient c hroom hsafe.1).write _ _ = _
    simpa [stepConfig_tape] using
      gn_shift_write_tape ι ambient c hroom hsafe
        (G1M.step c.state (c.tape c.head)).snd.fst

/-! ## Prefix-safe delegated runs -/

/-- Local step safety at every proper prefix of a run. -/
def G1RunSafe {W : Nat} (c : Configuration (M := G1M) W) (k : Nat) : Prop :=
  forall j, j < k -> G1LocalStepSafe (TM.runConfig (M := G1M) c j)

/-- Transition-tuple delegation at every proper prefix of a run. -/
def G1RunDelegates (M : TM.{u}) (ι : G1M.state -> M.state)
    {W : Nat} (c : Configuration (M := G1M) W) (k : Nat) : Prop :=
  forall j, j < k ->
    G1StepDelegates M ι (TM.runConfig (M := G1M) c j)

/-- Restrict prefix safety to a shorter run. -/
theorem G1RunSafe.mono {W : Nat} {c : Configuration (M := G1M) W} {j k : Nat}
    (h : G1RunSafe c k) (hjk : j <= k) : G1RunSafe c j := by
  intro t ht
  exact h t (by omega)

/-- Restrict prefix delegation to a shorter run. -/
theorem G1RunDelegates.mono {M : TM.{u}} {ι : G1M.state -> M.state}
    {W : Nat} {c : Configuration (M := G1M) W} {j k : Nat}
    (h : G1RunDelegates M ι c k) (hjk : j <= k) :
    G1RunDelegates M ι c j := by
  intro t ht
  exact h t (by omega)

/-- Prefix safety plus an initially local head derives locality at the run
endpoint, including the zero-step endpoint. -/
theorem gn_run_safe_endpoint_head {W k : Nat}
    (c : Configuration (M := G1M) W)
    (hhead : (c.head : Nat) < gnLocalSpan W) (hsafe : G1RunSafe c k) :
    ((TM.runConfig (M := G1M) c k).head : Nat) < gnLocalSpan W := by
  induction k with
  | zero => simpa using hhead
  | succ k ih =>
      rw [runConfig_succ]
      exact gn_local_step_safe_next_head _ (hsafe k (by omega))

/-- Exact run conjugacy, proved by induction from the tuple-level one-step
theorem. -/
theorem gn_delegate_run_shift {M : TM.{u}} {W N base k : Nat}
    (ι : G1M.state -> M.state) (ambient : Fin (M.tapeLength N) -> Bool)
    (c : Configuration (M := G1M) W)
    (hroom : base + gnLocalSpan W <= M.tapeLength N)
    (hhead : (c.head : Nat) < gnLocalSpan W)
    (hsafe : G1RunSafe c k) (hdelegate : G1RunDelegates M ι c k) :
    TM.runConfig (M := M) (gnShiftConfig M base ι ambient c hroom hhead) k =
      gnShiftConfig M base ι ambient (TM.runConfig (M := G1M) c k) hroom
        (gn_run_safe_endpoint_head c hhead hsafe) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [runConfig_succ]
      calc
        TM.stepConfig (M := M)
            (TM.runConfig (M := M)
              (gnShiftConfig M base ι ambient c hroom hhead) k) =
            TM.stepConfig (M := M)
              (gnShiftConfig M base ι ambient
                (TM.runConfig (M := G1M) c k) hroom
                (gn_run_safe_endpoint_head c hhead
                  (G1RunSafe.mono hsafe (by omega)))) :=
          congrArg (TM.stepConfig (M := M))
            (ih (G1RunSafe.mono hsafe (by omega))
              (G1RunDelegates.mono hdelegate (by omega)))
        _ = gnShiftConfig M base ι ambient
              (TM.stepConfig (M := G1M) (TM.runConfig (M := G1M) c k))
              hroom (gn_local_step_safe_next_head _ (hsafe k (by omega))) :=
          gn_delegate_step_shift ι ambient _ hroom
            (hsafe k (by omega)) (hdelegate k (by omega))

/-- At every prefix, every cell outside the shifted local footprint still
equals the caller's ambient tape. -/
theorem gn_delegate_run_shift_outside_prefix {M : TM.{u}}
    {W N base k j : Nat}
    (ι : G1M.state -> M.state) (ambient : Fin (M.tapeLength N) -> Bool)
    (c : Configuration (M := G1M) W)
    (hroom : base + gnLocalSpan W <= M.tapeLength N)
    (hhead : (c.head : Nat) < gnLocalSpan W)
    (hsafe : G1RunSafe c k) (hdelegate : G1RunDelegates M ι c k)
    (hj : j <= k) (i : Fin (M.tapeLength N))
    (hout : (i : Nat) < base ∨ base + gnLocalSpan W <= (i : Nat)) :
    (TM.runConfig (M := M)
      (gnShiftConfig M base ι ambient c hroom hhead) j).tape i = ambient i := by
  rw [gn_delegate_run_shift ι ambient c hroom hhead
    (G1RunSafe.mono hsafe hj) (G1RunDelegates.mono hdelegate hj)]
  exact gnShiftConfig_bit_outside ι ambient _ hroom _ i hout

/-- Endpoint specialization of pointwise outside preservation. -/
theorem gn_delegate_run_shift_outside {M : TM.{u}} {W N base k : Nat}
    (ι : G1M.state -> M.state) (ambient : Fin (M.tapeLength N) -> Bool)
    (c : Configuration (M := G1M) W)
    (hroom : base + gnLocalSpan W <= M.tapeLength N)
    (hhead : (c.head : Nat) < gnLocalSpan W)
    (hsafe : G1RunSafe c k) (hdelegate : G1RunDelegates M ι c k)
    (i : Fin (M.tapeLength N))
    (hout : (i : Nat) < base ∨ base + gnLocalSpan W <= (i : Nat)) :
    (TM.runConfig (M := M)
      (gnShiftConfig M base ι ambient c hroom hhead) k).tape i = ambient i :=
  gn_delegate_run_shift_outside_prefix ι ambient c hroom hhead hsafe hdelegate
    (Nat.le_refl k) i hout

/-! ## Honest arithmetic bridges -/

/-- GN-2's `W + 16 <= N` leaves eleven cells of base displacement while the
entire local footprint remains inside the target input word. -/
theorem gnLocalSpan_room_in_input_of_add_sixteen {W N base : Nat}
    (hWN : W + 16 <= N) (hbase : base <= 11) :
    base + gnLocalSpan W <= N := by
  simp [gnLocalSpan]
  omega

/-- Consequently GN-2's bound supplies physical room in a `G1M` target.  This
uses `G1M.tapeLength N >= N`; it is not a room theorem for arbitrary `M`. -/
theorem gn_g1_target_room_of_add_sixteen {W N base : Nat}
    (hWN : W + 16 <= N) (hbase : base <= 11) :
    base + gnLocalSpan W <= G1M.tapeLength N := by
  have hin := gnLocalSpan_room_in_input_of_add_sixteen hWN hbase
  apply le_trans hin
  change N <= N + g1Clock N + 1
  omega

/-- Base-zero form used by a future GN driver when its target is `G1M`. -/
theorem gn_g1_target_room_zero_of_add_sixteen {W N : Nat}
    (hWN : W + 16 <= N) : gnLocalSpan W <= G1M.tapeLength N := by
  simpa using gn_g1_target_room_of_add_sixteen (base := 0) hWN (by omega)

end Pnp3.Internal.PsubsetPpoly.TM
