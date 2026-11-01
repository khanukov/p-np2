import Complexity.Uniform.V1.FixedGammaPayloadDispatcherDeadline
import Mathlib.Data.Fintype.Card

/-!
# Gamma terminator to scratch bootstrap (Part A G2p-a)

A fixed 9-state, 27-row machine whose start configuration retags the *actual*
G2m dispatcher configuration at the dispatcher's common deadline.  Only the
control is replaced; the dispatcher verdict, the gamma width, and every parser
specification stay out of the control.

Write `N = a + m`.  On a matching tag whose physical terminator is at
`8 + zeros`, the run:

* normalizes the dispatcher head (`6` for positive width, `7` for width zero)
  to cell `8` at time `2`;
* scans the gamma zeros to the terminator and blanks it as a return marker,
  the only blank cell below `N`;
* scans to the first blank at `N`, writes `true` at scratch cell `N + 1`
  (always allocated, since the tape has `2a + m + B + 2` cells), steps back
  over `N`, scans left to the marker, restores the terminator, and halts in
  the absorbing `qTerm`.

The first terminal time is exactly `2*N - 11 - zeros` and the length-only
deadline is `2*N`.  The endpoint head is `8 + zeros`; the endpoint tape is
`contentTape` changed only at cell `N + 1`.  A failed gamma scan, where the
dispatcher stopped at the blank cell `N`, rejects in one step.

`qTerm` is the machine's accept tag only as an internal endpoint.  Nothing here
claims content acceptance, a decoded header value, or any pnp4 semantics.  This
is uniform-machine infrastructure, not P-vs-NP mainline progress.
-/

namespace Pnp3.Complexity.Uniform.V1.FixedGammaTerminatorScratchBootstrap

open PairEncoding

abbrev stateCount : Nat := 9

def qStart : Fin stateCount := ⟨0, by decide⟩
def qNormalize : Fin stateCount := ⟨1, by decide⟩
def qSeekTerm : Fin stateCount := ⟨2, by decide⟩
def qScanRight : Fin stateCount := ⟨3, by decide⟩
def qWriteScratch : Fin stateCount := ⟨4, by decide⟩
def qCrossBoundary : Fin stateCount := ⟨5, by decide⟩
def qScanLeft : Fin stateCount := ⟨6, by decide⟩
def qTerm : Fin stateCount := ⟨7, by decide⟩
def qReject : Fin stateCount := ⟨8, by decide⟩

/-- The complete fixed 9-state, 27-row table. -/
def raw (q : Fin stateCount) (s : Option Bool) :
    Fin stateCount × Option Bool × Move :=
  match q.1 with
  | 0 => match s with
    | some true => (qNormalize, some true, .right)
    | some false => (qNormalize, some false, .stay)
    | none => (qReject, none, .stay)
  | 1 => match s with
    | some false => (qSeekTerm, some false, .right)
    | s => (qReject, s, .stay)
  | 2 => match s with
    | some false => (qSeekTerm, some false, .right)
    | some true => (qScanRight, none, .right)
    | none => (qReject, none, .stay)
  | 3 => match s with
    | some b => (qScanRight, some b, .right)
    | none => (qWriteScratch, none, .right)
  | 4 => match s with
    | none => (qCrossBoundary, some true, .left)
    | s => (qReject, s, .stay)
  | 5 => match s with
    | none => (qScanLeft, none, .left)
    | s => (qReject, s, .stay)
  | 6 => match s with
    | some b => (qScanLeft, some b, .left)
    | none => (qTerm, some true, .stay)
  | 7 => (qTerm, s, .stay)
  | _ => (qReject, s, .stay)

def machine : UniformTM where
  stateCount := stateCount
  start := qStart
  accept := qTerm
  reject := qReject
  accept_ne_reject := by decide
  rawStep := raw

/-- Honest input ABI: only the control of the actual dispatcher configuration
is replaced. -/
def retagDispatcher {N B : Nat} (c : Config FixedGammaPayloadDispatcher.stateCount N B) :
    Config stateCount N B := ⟨qStart, c.head, c.tape⟩

def startConfig {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) :
    Config stateCount (pairLength a m) B :=
  retagDispatcher (FixedGammaPayloadDispatcher.machine.run
    (FixedGammaPayloadDispatcherDeadline.deadline (a + m))
    (FixedGammaPayloadDispatcher.startConfig B x w))

/-- First terminal time for gamma width `zeros` over `N` content cells. -/
def exactClock (N zeros : Nat) : Nat := 2 * N - 11 - zeros

/-- Public length-only deadline. -/
def deadline (N : Nat) : Nat := 2 * N

/-- Content with the terminator cell `8 + zeros` blanked as the return marker. -/
def markedTape {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) (zeros : Nat) :
    Fin (tapeLength (pairLength a m) B) → Option Bool := fun i =>
  if i.val = 8 + zeros then none else FixedPairContentMarkerErase.contentTape B x w i

/-- The marked tape after `true` is written at scratch cell `a + m + 1`. -/
def scratchMarkedTape {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m)
    (zeros : Nat) : Fin (tapeLength (pairLength a m) B) → Option Bool := fun i =>
  if i.val = a + m + 1 then some true else markedTape B x w zeros i

/-- Endpoint tape: `contentTape` with `true` at scratch cell `a + m + 1`. -/
def scratchTape {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) :
    Fin (tapeLength (pairLength a m) B) → Option Bool := fun i =>
  if i.val = a + m + 1 then some true else FixedPairContentMarkerErase.contentTape B x w i

/-- Budget-free control schedule of a successful run. -/
def traceState (N zeros s : Nat) : Fin stateCount :=
  if s = 0 then qStart
  else if s = 1 then qNormalize
  else if s ≤ 2 + zeros then qSeekTerm
  else if s ≤ N - 6 then qScanRight
  else if s = N - 5 then qWriteScratch
  else if s = N - 4 then qCrossBoundary
  else if s ≤ 2 * N - 12 - zeros then qScanLeft
  else qTerm

/-- Budget-free head schedule of a successful run. -/
def traceHead (N zeros s : Nat) : Nat :=
  if s = 0 then (if zeros = 0 then 7 else 6)
  else if s ≤ N - 5 then s + 6
  else if s ≤ 2 * N - 12 - zeros then 2 * N - 4 - s
  else 8 + zeros

/-- Tape schedule of a successful run. -/
def traceTape {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) (zeros s : Nat) :
    Fin (tapeLength (pairLength a m) B) → Option Bool := fun i =>
  if s ≤ 2 + zeros then FixedPairContentMarkerErase.contentTape B x w i
  else if s ≤ a + m - 5 then markedTape B x w zeros i
  else if s ≤ 2 * (a + m) - 12 - zeros then scratchMarkedTape B x w zeros i
  else scratchTape B x w i

/-- Every row, pinned literally, with the resource counts. -/
theorem table_and_resource_pins :
    machine.step qStart none = (qReject, none, .stay) ∧
    machine.step qStart (some false) = (qNormalize, some false, .stay) ∧
    machine.step qStart (some true) = (qNormalize, some true, .right) ∧
    machine.step qNormalize none = (qReject, none, .stay) ∧
    machine.step qNormalize (some false) = (qSeekTerm, some false, .right) ∧
    machine.step qNormalize (some true) = (qReject, some true, .stay) ∧
    machine.step qSeekTerm none = (qReject, none, .stay) ∧
    machine.step qSeekTerm (some false) = (qSeekTerm, some false, .right) ∧
    machine.step qSeekTerm (some true) = (qScanRight, none, .right) ∧
    machine.step qScanRight none = (qWriteScratch, none, .right) ∧
    machine.step qScanRight (some false) = (qScanRight, some false, .right) ∧
    machine.step qScanRight (some true) = (qScanRight, some true, .right) ∧
    machine.step qWriteScratch none = (qCrossBoundary, some true, .left) ∧
    machine.step qWriteScratch (some false) = (qReject, some false, .stay) ∧
    machine.step qWriteScratch (some true) = (qReject, some true, .stay) ∧
    machine.step qCrossBoundary none = (qScanLeft, none, .left) ∧
    machine.step qCrossBoundary (some false) = (qReject, some false, .stay) ∧
    machine.step qCrossBoundary (some true) = (qReject, some true, .stay) ∧
    machine.step qScanLeft none = (qTerm, some true, .stay) ∧
    machine.step qScanLeft (some false) = (qScanLeft, some false, .left) ∧
    machine.step qScanLeft (some true) = (qScanLeft, some true, .left) ∧
    machine.step qTerm none = (qTerm, none, .stay) ∧
    machine.step qTerm (some false) = (qTerm, some false, .stay) ∧
    machine.step qTerm (some true) = (qTerm, some true, .stay) ∧
    machine.step qReject none = (qReject, none, .stay) ∧
    machine.step qReject (some false) = (qReject, some false, .stay) ∧
    machine.step qReject (some true) = (qReject, some true, .stay) ∧
    machine.stateCount = 9 ∧ machine.start = qStart ∧
    machine.accept = qTerm ∧ machine.reject = qReject ∧
    qStart.val = 0 ∧ qNormalize.val = 1 ∧ qSeekTerm.val = 2 ∧ qScanRight.val = 3 ∧
    qWriteScratch.val = 4 ∧ qCrossBoundary.val = 5 ∧ qScanLeft.val = 6 ∧
    qTerm.val = 7 ∧ qReject.val = 8 ∧
    Fintype.card (Fin machine.stateCount × Option Bool) = 27 := by
  repeat' apply And.intro
  all_goals rfl

theorem per_step_budget_independent : ∀ q s, machine.step q s = machine.rawStep q s := by
  intro q s
  fin_cases q <;> cases s with
  | none => rfl
  | some b => cases b <;> rfl

theorem endpoints_absorb {N B : Nat} (c : Config stateCount N B) :
    (c.state = qTerm → ∀ n, machine.run n c = c) ∧
    (c.state = qReject → ∀ n, machine.run n c = c) :=
  ⟨fun h n => machine.run_accept c h n, fun h n => machine.run_reject c h n⟩

theorem handoff_exact {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let p := FixedGammaPayloadDispatcher.machine.run
      (FixedGammaPayloadDispatcherDeadline.deadline (a + m))
      (FixedGammaPayloadDispatcher.startConfig B x w)
    let c := startConfig B x w
    c = retagDispatcher p ∧ c.state = machine.start ∧ c.head = p.head ∧
      c.tape = p.tape :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The subtraction in `exactClock` never truncates on a decoded width. -/
theorem exactClock_add {N zeros : Nat} (hN : 9 + zeros ≤ N) :
    exactClock N zeros + zeros + 11 = 2 * N := by
  unfold exactClock
  omega

theorem exactClock_le_deadline (N zeros : Nat) : exactClock N zeros ≤ deadline N := by
  unfold exactClock deadline
  omega

/-- The blanked terminator is the unique blank cell below the boundary. -/
theorem marker_unique {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (i : Fin (tapeLength (pairLength a m) B)) :
    markedTape B x w zeros i = none ↔ i.val = 8 + zeros ∨ a + m ≤ i.val := by
  unfold markedTape FixedPairContentMarkerErase.contentTape
  by_cases h8 : i.val = 8 + zeros
  · rw [if_pos h8]
    exact ⟨fun _ => Or.inl h8, fun _ => rfl⟩
  · rw [if_neg h8]
    by_cases hlt : i.val < a + m
    · rw [dif_pos hlt]
      exact ⟨(fun h => nomatch h), fun h => absurd h (by omega)⟩
    · rw [dif_neg hlt]
      exact ⟨fun _ => Or.inr (by omega), fun _ => rfl⟩

/-- The endpoint tape restores every source cell, keeps the boundary blank,
holds `true` at the scratch cell, and is blank afterwards. -/
theorem scratchTape_layout {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    (∀ j : Fin (a + m), scratchTape B x w
      ⟨j.val, by unfold tapeLength pairLength; omega⟩ = some (Fin.append x w j)) ∧
    scratchTape B x w ⟨a + m, by unfold tapeLength pairLength; omega⟩ = none ∧
    scratchTape B x w ⟨a + m + 1, by unfold tapeLength pairLength; omega⟩ = some true ∧
    ∀ i : Fin (tapeLength (pairLength a m) B), a + m + 1 < i.val →
      scratchTape B x w i = none := by
  refine ⟨fun j => ?_, ?_, ?_, fun i hi => ?_⟩
  · unfold scratchTape FixedPairContentMarkerErase.contentTape
    rw [if_neg (show ¬ j.val = a + m + 1 by omega), dif_pos j.isLt]
  · unfold scratchTape FixedPairContentMarkerErase.contentTape
    rw [if_neg (show ¬ a + m = a + m + 1 by omega), dif_neg (show ¬ a + m < a + m by omega)]
  · unfold scratchTape
    rw [if_pos rfl]
  · unfold scratchTape FixedPairContentMarkerErase.contentTape
    rw [if_neg (show ¬ i.val = a + m + 1 by omega), dif_neg (show ¬ i.val < a + m by omega)]

/-! ### Address-level execution invariant -/

private def content {a m : Nat} (x : Bitstring a) (w : Bitstring m) : Nat → Option Bool :=
  FixedContentTagGate.physicalSymbol (Fin.append x w)

private def marked {a m : Nat} (x : Bitstring a) (w : Bitstring m) (zeros k : Nat) :
    Option Bool :=
  if k = 8 + zeros then none else content x w k

private def scratchMarked {a m : Nat} (x : Bitstring a) (w : Bitstring m) (zeros k : Nat) :
    Option Bool :=
  if k = a + m + 1 then some true else marked x w zeros k

private def scratch {a m : Nat} (x : Bitstring a) (w : Bitstring m) (k : Nat) :
    Option Bool :=
  if k = a + m + 1 then some true else content x w k

private def tapeAt {a m : Nat} (x : Bitstring a) (w : Bitstring m) (zeros s k : Nat) :
    Option Bool :=
  if s ≤ 2 + zeros then content x w k
  else if s ≤ a + m - 5 then marked x w zeros k
  else if s ≤ 2 * (a + m) - 12 - zeros then scratchMarked x w zeros k
  else scratch x w k

/-- Control, numeric head, and every tape cell read through its address. -/
private def At {n B : Nat} (c : Config stateCount n B) (q : Fin stateCount) (k : Nat)
    (T : Nat → Option Bool) : Prop :=
  c.state = q ∧ c.head.val = k ∧ ∀ i, c.tape i = T i.val

private def shift (k : Nat) : Move → Nat
  | .left => k - 1
  | .stay => k
  | .right => k + 1

private theorem step_at {n B : Nat} {c : Config stateCount n B} {q q' : Fin stateCount}
    {k k' : Nat} {T T' : Nat → Option Bool} {r s' : Option Bool} {mv : Move}
    (hc : At c q k T) (hread : T k = r) (hrow : machine.step q r = (q', s', mv))
    (hk : shift k mv = k') (hfit : mv = .right → k + 1 < tapeLength n B)
    (hwrite : T' k = s') (hkeep : ∀ i, i ≠ k → T' i = T i) :
    At (machine.stepConfig c) q' k' T' := by
  obtain ⟨hq, hh, ht⟩ := hc
  have haction : machine.step c.state (c.tape c.head) = (q', s', mv) := by
    rw [hq, ht, hh, hread, hrow]
  refine ⟨?_, ?_, fun i => ?_⟩
  · change (machine.step c.state (c.tape c.head)).1 = q'
    rw [haction]
  · change (moveHead c.head (machine.step c.state (c.tape c.head)).2.2).val = k'
    rw [haction, ← hk]
    cases mv with
    | left =>
        change c.head.val - 1 = k - 1
        rw [hh]
    | stay => exact hh
    | right =>
        have hlt : c.head.val + 1 < tapeLength n B := by
          rw [hh]
          exact hfit rfl
        unfold moveHead
        rw [dif_pos hlt]
        change c.head.val + 1 = k + 1
        rw [hh]
  · change (if i = c.head then (machine.step c.state (c.tape c.head)).2.1
      else c.tape i) = T' i.val
    rw [haction]
    by_cases hi : i.val = k
    · rw [if_pos (Fin.ext (hi.trans hh.symm)), hi, hwrite]
    · rw [if_neg (fun h => hi (by rw [h, hh])), hkeep i.val hi, ht]

private theorem stepAt_right {n B t : Nat} {c : Config stateCount n B}
    {q q' : Fin stateCount} {k k' : Nat} {T T' : Nat → Option Bool} {r s' : Option Bool}
    (hc : At (machine.run t c) q k T) (hread : T k = r)
    (hrow : machine.step q r = (q', s', .right)) (hk : k + 1 = k')
    (hfit : k + 1 < tapeLength n B) (hwrite : T' k = s')
    (hkeep : ∀ i, i ≠ k → T' i = T i) : At (machine.run (t + 1) c) q' k' T' :=
  step_at hc hread hrow hk (fun _ => hfit) hwrite hkeep

private theorem stepAt_left {n B t : Nat} {c : Config stateCount n B}
    {q q' : Fin stateCount} {k k' : Nat} {T T' : Nat → Option Bool} {r s' : Option Bool}
    (hc : At (machine.run t c) q k T) (hread : T k = r)
    (hrow : machine.step q r = (q', s', .left)) (hk : k - 1 = k')
    (hwrite : T' k = s') (hkeep : ∀ i, i ≠ k → T' i = T i) :
    At (machine.run (t + 1) c) q' k' T' :=
  step_at hc hread hrow hk (fun h => nomatch h) hwrite hkeep

private theorem stepAt_stay {n B t : Nat} {c : Config stateCount n B}
    {q q' : Fin stateCount} {k k' : Nat} {T T' : Nat → Option Bool} {r s' : Option Bool}
    (hc : At (machine.run t c) q k T) (hread : T k = r)
    (hrow : machine.step q r = (q', s', .stay)) (hk : k = k')
    (hwrite : T' k = s') (hkeep : ∀ i, i ≠ k → T' i = T i) :
    At (machine.run (t + 1) c) q' k' T' :=
  step_at hc hread hrow hk (fun h => nomatch h) hwrite hkeep

private theorem row_scanRight (b : Bool) :
    machine.step qScanRight (some b) = (qScanRight, some b, .right) := by
  cases b <;> rfl

private theorem row_scanLeft (b : Bool) :
    machine.step qScanLeft (some b) = (qScanLeft, some b, .left) := by
  cases b <;> rfl

private theorem content_lt {a m : Nat} (x : Bitstring a) (w : Bitstring m) {k : Nat}
    (hk : k < a + m) : ∃ b, content x w k = some b :=
  ⟨Fin.append x w ⟨k, hk⟩, by
    unfold content FixedContentTagGate.physicalSymbol
    rw [dif_pos hk]⟩

private theorem content_ge {a m : Nat} (x : Bitstring a) (w : Bitstring m) {k : Nat}
    (hk : a + m ≤ k) : content x w k = none := by
  unfold content FixedContentTagGate.physicalSymbol
  rw [dif_neg (show ¬ k < a + m by omega)]

private theorem tapeAt_off {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    {zeros s k : Nat} (h1 : k ≠ 8 + zeros) (h2 : k ≠ a + m + 1) :
    tapeAt x w zeros s k = content x w k := by
  simp only [tapeAt, marked, scratchMarked, scratch, if_neg h1, if_neg h2, ite_self]

private theorem state_start {N zeros s : Nat} (h : s = 0) :
    traceState N zeros s = qStart := by
  subst h
  rfl

private theorem state_normalize {N zeros s : Nat} (h : s = 1) :
    traceState N zeros s = qNormalize := by
  subst h
  rfl

private theorem state_seek {N zeros s : Nat} (h1 : 2 ≤ s) (h2 : s ≤ 2 + zeros) :
    traceState N zeros s = qSeekTerm := by
  unfold traceState
  split_ifs <;> first | rfl | omega

private theorem state_right {N zeros s : Nat} (h1 : 2 + zeros < s) (h2 : s ≤ N - 6) :
    traceState N zeros s = qScanRight := by
  unfold traceState
  split_ifs <;> first | rfl | omega

private theorem state_write {N zeros s : Nat} (hN : 9 + zeros ≤ N) (h : s = N - 5) :
    traceState N zeros s = qWriteScratch := by
  unfold traceState
  split_ifs <;> first | rfl | omega

private theorem state_cross {N zeros s : Nat} (hN : 9 + zeros ≤ N) (h : s = N - 4) :
    traceState N zeros s = qCrossBoundary := by
  unfold traceState
  split_ifs <;> first | rfl | omega

private theorem state_left {N zeros s : Nat} (hN : 9 + zeros ≤ N) (h1 : N - 4 < s)
    (h2 : s ≤ 2 * N - 12 - zeros) : traceState N zeros s = qScanLeft := by
  unfold traceState
  split_ifs <;> first | rfl | omega

private theorem state_term {N zeros s : Nat} (hN : 9 + zeros ≤ N)
    (h : 2 * N - 12 - zeros < s) : traceState N zeros s = qTerm := by
  unfold traceState
  split_ifs <;> first | rfl | omega

private theorem head_start {N zeros s : Nat} (h : s = 0) :
    traceHead N zeros s = if zeros = 0 then 7 else 6 := by
  subst h
  rfl

private theorem head_right {N zeros s : Nat} (h1 : 1 ≤ s) (h2 : s ≤ N - 5) :
    traceHead N zeros s = s + 6 := by
  unfold traceHead
  split_ifs <;> omega

private theorem head_left {N zeros s : Nat} (h1 : N - 5 < s)
    (h2 : s ≤ 2 * N - 12 - zeros) : traceHead N zeros s = 2 * N - 4 - s := by
  unfold traceHead
  split_ifs <;> omega

private theorem head_term {N zeros s : Nat} (hN : 9 + zeros ≤ N)
    (h : 2 * N - 12 - zeros < s) : traceHead N zeros s = 8 + zeros := by
  unfold traceHead
  split_ifs <;> omega

private theorem head_bounds {N zeros s : Nat} (hN : 9 + zeros ≤ N) :
    6 ≤ traceHead N zeros s ∧ traceHead N zeros s ≤ N + 1 ∧
      (traceHead N zeros s = N + 1 → s = N - 5) := by
  unfold traceHead
  split_ifs <;> omega

private theorem tape_content {a m : Nat} {x : Bitstring a} {w : Bitstring m}
    {zeros s : Nat} (h : s ≤ 2 + zeros) : tapeAt x w zeros s = content x w := by
  funext k
  unfold tapeAt
  rw [if_pos h]

private theorem tape_marked {a m : Nat} {x : Bitstring a} {w : Bitstring m}
    {zeros s : Nat} (h1 : 2 + zeros < s) (h2 : s ≤ a + m - 5) :
    tapeAt x w zeros s = marked x w zeros := by
  funext k
  unfold tapeAt
  rw [if_neg (show ¬ s ≤ 2 + zeros by omega), if_pos h2]

private theorem tape_scratchMarked {a m : Nat} {x : Bitstring a} {w : Bitstring m}
    {zeros s : Nat} (h0 : 2 + zeros < s) (h1 : a + m - 5 < s)
    (h2 : s ≤ 2 * (a + m) - 12 - zeros) : tapeAt x w zeros s = scratchMarked x w zeros := by
  funext k
  unfold tapeAt
  rw [if_neg (show ¬ s ≤ 2 + zeros by omega), if_neg (show ¬ s ≤ a + m - 5 by omega),
    if_pos h2]

private theorem tape_scratch {a m : Nat} {x : Bitstring a} {w : Bitstring m}
    {zeros s : Nat} (h0 : 2 + zeros < s) (h1 : a + m - 5 < s)
    (h2 : 2 * (a + m) - 12 - zeros < s) : tapeAt x w zeros s = scratch x w := by
  funext k
  unfold tapeAt
  rw [if_neg (show ¬ s ≤ 2 + zeros by omega), if_neg (show ¬ s ≤ a + m - 5 by omega),
    if_neg (show ¬ s ≤ 2 * (a + m) - 12 - zeros by omega)]

private theorem start_at {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros) :
    At (startConfig B x w) qStart (if zeros = 0 then 7 else 6) (content x w) := by
  obtain ⟨htape, hcases⟩ :=
    FixedGammaPayloadDispatcherDeadline.tagged_endpoint_classification (B := B) x w htag
  have ht : (startConfig B x w).tape = FixedPairContentMarkerErase.contentTape B x w :=
    htape
  refine ⟨rfl, ?_, fun i => by rw [ht]; rfl⟩
  rw [hg] at hcases
  rcases hcases with ⟨_, _, h⟩ | ⟨_, hh, h⟩ | ⟨z, hz, hpos, hh, _⟩
  · cases h
  · obtain rfl : zeros = 0 := Option.some.inj h
    rw [if_pos rfl]
    exact hh
  · obtain rfl : zeros = z := Option.some.inj hz
    rw [if_neg (by omega)]
    exact hh

private theorem malformed_start_at {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = none) :
    At (startConfig B x w) qStart (a + m) (content x w) := by
  obtain ⟨htape, hcases⟩ :=
    FixedGammaPayloadDispatcherDeadline.tagged_endpoint_classification (B := B) x w htag
  have ht : (startConfig B x w).tape = FixedPairContentMarkerErase.contentTape B x w :=
    htape
  refine ⟨rfl, ?_, fun i => by rw [ht]; rfl⟩
  rw [hg] at hcases
  rcases hcases with ⟨_, hh, _⟩ | ⟨_, _, h⟩ | ⟨_, h, _⟩
  · exact hh
  · cases h
  · cases h

private theorem malformed_at {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = none) (s : Nat) :
    At (machine.run s (startConfig B x w)) (if s = 0 then qStart else qReject) (a + m)
      (content x w) := by
  induction s with
  | zero =>
      rw [if_pos rfl]
      exact malformed_start_at x w htag hg
  | succ s ih =>
      rw [if_neg (show ¬ s + 1 = 0 by omega)]
      by_cases hs : s = 0
      · rw [if_pos hs] at ih
        exact stepAt_stay ih (content_ge x w le_rfl) rfl rfl (content_ge x w le_rfl)
          (fun _ _ => rfl)
      · rw [if_neg hs] at ih
        exact stepAt_stay ih rfl (machine.step_reject _) rfl rfl (fun _ _ => rfl)

private theorem trace_at {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros) (s : Nat) :
    At (machine.run s (startConfig B x w)) (traceState (a + m) zeros s)
      (traceHead (a + m) zeros s) (tapeAt x w zeros s) := by
  have hgc := (FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 zeros hg
  have hN : 9 + zeros ≤ a + m := by have := hgc.1; omega
  have hL : a + m + 2 ≤ tapeLength (pairLength a m) B := by
    unfold tapeLength pairLength
    omega
  have hterm : content x w (8 + zeros) = some true := hgc.2.1
  have hzero : ∀ i, i < zeros → content x w (8 + i) = some false := hgc.2.2
  have hall := ((FixedContentTagGate.tag_contract (Fin.append x w)).2.2.2.2.2.2.2.2.1).1 htag
  have h6' := hall ⟨6, by decide⟩
  have h7' := hall ⟨7, by decide⟩
  have h6 : content x w 6 = some true := h6'
  have h7 : content x w 7 = some false := h7'
  induction s with
  | zero =>
      rw [state_start rfl, head_start rfl, tape_content (by omega)]
      exact start_at x w htag hg
  | succ s ih =>
      rcases (show s = 0 ∨ s = 1 ∨ (2 ≤ s ∧ s < 2 + zeros) ∨ s = 2 + zeros ∨
          (2 + zeros < s ∧ s < a + m - 6) ∨ s = a + m - 6 ∨ s = a + m - 5 ∨
          s = a + m - 4 ∨ (a + m - 4 < s ∧ s < 2 * (a + m) - 12 - zeros) ∨
          s = 2 * (a + m) - 12 - zeros ∨ 2 * (a + m) - 12 - zeros < s by omega)
        with h | h | h | h | h | h | h | h | h | h | h
      · -- Normalize from head `7` (zero width) or `6` (positive width).
        rw [state_start h, head_start h, tape_content (by omega)] at ih
        rw [state_normalize (s := s + 1) (by omega),
          head_right (s := s + 1) (by omega) (by omega), tape_content (s := s + 1) (by omega)]
        by_cases hz : zeros = 0
        · rw [if_pos hz] at ih
          exact stepAt_stay ih h7 rfl (by omega) h7 (fun _ _ => rfl)
        · rw [if_neg hz] at ih
          exact stepAt_right ih h6 rfl (by omega) (by omega) h6 (fun _ _ => rfl)
      · rw [state_normalize h, head_right (by omega) (by omega), tape_content (by omega)] at ih
        rw [state_seek (s := s + 1) (by omega) (by omega),
          head_right (s := s + 1) (by omega) (by omega), tape_content (s := s + 1) (by omega)]
        have hr : content x w (s + 6) = some false := by
          rw [show s + 6 = 7 by omega]
          exact h7
        exact stepAt_right ih hr rfl (by omega) (by omega) hr (fun _ _ => rfl)
      · -- Scan the gamma zeros.
        rw [state_seek (by omega) (by omega), head_right (by omega) (by omega),
          tape_content (by omega)] at ih
        rw [state_seek (s := s + 1) (by omega) (by omega),
          head_right (s := s + 1) (by omega) (by omega), tape_content (s := s + 1) (by omega)]
        have hr : content x w (s + 6) = some false := by
          have hs := hzero (s - 2) (by omega)
          rwa [show 8 + (s - 2) = s + 6 by omega] at hs
        exact stepAt_right ih hr rfl (by omega) (by omega) hr (fun _ _ => rfl)
      · -- Blank the terminator as the return marker.
        rw [state_seek (by omega) (by omega), head_right (by omega) (by omega),
          tape_content (by omega)] at ih
        rw [state_right (s := s + 1) (by omega) (by omega),
          head_right (s := s + 1) (by omega) (by omega),
          tape_marked (s := s + 1) (by omega) (by omega)]
        have hr : content x w (s + 6) = some true := by
          rw [show s + 6 = 8 + zeros by omega]
          exact hterm
        refine stepAt_right ih hr rfl (by omega) (by omega) ?_ (fun i hi => ?_)
        · unfold marked
          rw [if_pos (show s + 6 = 8 + zeros by omega)]
        · unfold marked
          rw [if_neg (show ¬ i = 8 + zeros by omega)]
      · -- Scan the remaining content to the boundary.
        rw [state_right (by omega) (by omega), head_right (by omega) (by omega),
          tape_marked (by omega) (by omega)] at ih
        rw [state_right (s := s + 1) (by omega) (by omega),
          head_right (s := s + 1) (by omega) (by omega),
          tape_marked (s := s + 1) (by omega) (by omega)]
        obtain ⟨b, hb⟩ := content_lt x w (k := s + 6) (by omega)
        have hr : marked x w zeros (s + 6) = some b := by
          unfold marked
          rw [if_neg (show ¬ s + 6 = 8 + zeros by omega)]
          exact hb
        exact stepAt_right ih hr (row_scanRight b) (by omega) (by omega) hr (fun _ _ => rfl)
      · -- Cross the blank boundary cell `a + m`.
        rw [state_right (by omega) (by omega), head_right (by omega) (by omega),
          tape_marked (by omega) (by omega)] at ih
        rw [state_write (s := s + 1) hN (by omega),
          head_right (s := s + 1) (by omega) (by omega),
          tape_marked (s := s + 1) (by omega) (by omega)]
        have hr : marked x w zeros (s + 6) = none := by
          unfold marked
          rw [if_neg (show ¬ s + 6 = 8 + zeros by omega)]
          exact content_ge x w (by omega)
        exact stepAt_right ih hr rfl (by omega) (by omega) hr (fun _ _ => rfl)
      · -- Write `true` at the scratch cell `a + m + 1`.
        rw [state_write hN h, head_right (by omega) (by omega),
          tape_marked (by omega) (by omega)] at ih
        rw [state_cross (s := s + 1) hN (by omega),
          head_left (s := s + 1) (by omega) (by omega),
          tape_scratchMarked (s := s + 1) (by omega) (by omega) (by omega)]
        have hr : marked x w zeros (s + 6) = none := by
          unfold marked
          rw [if_neg (show ¬ s + 6 = 8 + zeros by omega)]
          exact content_ge x w (by omega)
        refine stepAt_left ih hr rfl (by omega) ?_ (fun i hi => ?_)
        · unfold scratchMarked
          rw [if_pos (show s + 6 = a + m + 1 by omega)]
        · unfold scratchMarked
          rw [if_neg (show ¬ i = a + m + 1 by omega)]
      · -- Step back over the boundary.
        rw [state_cross hN h, head_left (by omega) (by omega),
          tape_scratchMarked (by omega) (by omega) (by omega)] at ih
        rw [state_left (s := s + 1) hN (by omega) (by omega),
          head_left (s := s + 1) (by omega) (by omega),
          tape_scratchMarked (s := s + 1) (by omega) (by omega) (by omega)]
        have hr : scratchMarked x w zeros (2 * (a + m) - 4 - s) = none := by
          unfold scratchMarked marked
          rw [if_neg (show ¬ 2 * (a + m) - 4 - s = a + m + 1 by omega),
            if_neg (show ¬ 2 * (a + m) - 4 - s = 8 + zeros by omega)]
          exact content_ge x w (by omega)
        exact stepAt_left ih hr rfl (by omega) hr (fun _ _ => rfl)
      · -- Scan left to the marker.
        rw [state_left hN (by omega) (by omega), head_left (by omega) (by omega),
          tape_scratchMarked (by omega) (by omega) (by omega)] at ih
        rw [state_left (s := s + 1) hN (by omega) (by omega),
          head_left (s := s + 1) (by omega) (by omega),
          tape_scratchMarked (s := s + 1) (by omega) (by omega) (by omega)]
        obtain ⟨b, hb⟩ := content_lt x w (k := 2 * (a + m) - 4 - s) (by omega)
        have hr : scratchMarked x w zeros (2 * (a + m) - 4 - s) = some b := by
          unfold scratchMarked marked
          rw [if_neg (show ¬ 2 * (a + m) - 4 - s = a + m + 1 by omega),
            if_neg (show ¬ 2 * (a + m) - 4 - s = 8 + zeros by omega)]
          exact hb
        exact stepAt_left ih hr (row_scanLeft b) (by omega) hr (fun _ _ => rfl)
      · -- Restore the terminator and halt.
        rw [state_left hN (by omega) (by omega), head_left (by omega) (by omega),
          tape_scratchMarked (by omega) (by omega) (by omega)] at ih
        rw [state_term (s := s + 1) hN (by omega), head_term (s := s + 1) hN (by omega),
          tape_scratch (s := s + 1) (by omega) (by omega) (by omega)]
        have hr : scratchMarked x w zeros (2 * (a + m) - 4 - s) = none := by
          unfold scratchMarked marked
          rw [if_neg (show ¬ 2 * (a + m) - 4 - s = a + m + 1 by omega),
            if_pos (show 2 * (a + m) - 4 - s = 8 + zeros by omega)]
        refine stepAt_stay ih hr rfl (by omega) ?_ (fun i hi => ?_)
        · unfold scratch
          rw [if_neg (show ¬ 2 * (a + m) - 4 - s = a + m + 1 by omega),
            show 2 * (a + m) - 4 - s = 8 + zeros by omega]
          exact hterm
        · unfold scratch scratchMarked marked
          by_cases hi1 : i = a + m + 1
          · rw [if_pos hi1, if_pos hi1]
          · rw [if_neg hi1, if_neg hi1, if_neg (show ¬ i = 8 + zeros by omega)]
      · -- Absorbing endpoint.
        rw [state_term hN h, head_term hN h, tape_scratch (by omega) (by omega) h] at ih
        rw [state_term (s := s + 1) hN (by omega), head_term (s := s + 1) hN (by omega),
          tape_scratch (s := s + 1) (by omega) (by omega) (by omega)]
        exact stepAt_stay ih rfl (machine.step_accept _) rfl rfl (fun _ _ => rfl)

/-! ### Public execution theorems -/

/-- Exact trace at every time: control, numeric head, and whole tape. -/
theorem run_trace {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (s : Nat) :
    let d := machine.run s (startConfig B x w)
    d.state = traceState (a + m) zeros s ∧ d.head.val = traceHead (a + m) zeros s ∧
      d.tape = traceTape B x w zeros s := by
  obtain ⟨hq, hh, ht⟩ := trace_at (B := B) x w htag hg s
  exact ⟨hq, hh, funext ht⟩

/-- From the exact clock on, the endpoint is `qTerm` at head `8 + zeros` with the
scratch tape. -/
theorem post_clock_absorption {a m B zeros : Nat} (x : Bitstring a)
    (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (s : Nat) (hs : exactClock (a + m) zeros ≤ s) :
    let d := machine.run s (startConfig B x w)
    d.state = qTerm ∧ d.head.val = 8 + zeros ∧ d.tape = scratchTape B x w := by
  have hN : 9 + zeros ≤ a + m := by
    have := ((FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 zeros hg).1
    omega
  have hlt : 2 * (a + m) - 12 - zeros < s := by
    unfold exactClock at hs
    omega
  obtain ⟨hq, hh, ht⟩ := trace_at (B := B) x w htag hg s
  rw [state_term hN hlt] at hq
  rw [head_term hN hlt] at hh
  rw [tape_scratch (by omega) (by omega) hlt] at ht
  exact ⟨hq, hh, funext ht⟩

theorem run_exact {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros) :
    let d := machine.run (exactClock (a + m) zeros) (startConfig B x w)
    d.state = qTerm ∧ d.head.val = 8 + zeros ∧ d.tape = scratchTape B x w :=
  post_clock_absorption x w htag hg _ le_rfl

theorem run_deadline {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros) :
    let d := machine.run (deadline (a + m)) (startConfig B x w)
    d.state = qTerm ∧ d.head.val = 8 + zeros ∧ d.tape = scratchTape B x w :=
  post_clock_absorption x w htag hg _ (exactClock_le_deadline _ _)

/-- The exact clock is the strict first time either terminal state appears. -/
theorem strict_first_terminal {a m B zeros : Nat} (x : Bitstring a)
    (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros) :
    (∀ s, s < exactClock (a + m) zeros →
      (machine.run s (startConfig B x w)).state ≠ qTerm ∧
      (machine.run s (startConfig B x w)).state ≠ qReject) ∧
    (machine.run (exactClock (a + m) zeros) (startConfig B x w)).state = qTerm := by
  obtain ⟨hend, _, _⟩ := run_exact (B := B) x w htag hg
  refine ⟨fun s hs => ?_, hend⟩
  obtain ⟨hq, _, _⟩ := trace_at (B := B) x w htag hg s
  rw [hq]
  unfold exactClock at hs
  unfold traceState
  split_ifs <;> first | decide | (exfalso; omega)

/-- On every tagged input, no transition at any time clamps at either end of the
tape, for every budget including `B = 0`. -/
theorem no_boundary_clamp {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true) (s : Nat) :
    let c := machine.run s (startConfig B x w)
    let move := (machine.step c.state (c.tape c.head)).2.2
    (move = .right → c.head.val + 1 < tapeLength (pairLength a m) B) ∧
    (move = .left → 0 < c.head.val) := by
  cases hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) with
  | none =>
      obtain ⟨hq, hh, ht⟩ := malformed_at (B := B) x w htag hg s
      dsimp only
      rw [hq, ht, hh, content_ge x w le_rfl]
      have hstay : (machine.step (if s = 0 then qStart else qReject) none).2.2 = .stay := by
        split_ifs <;> rfl
      rw [hstay]
      exact ⟨nofun, nofun⟩
  | some zeros =>
      have hN : 9 + zeros ≤ a + m := by
        have := ((FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 zeros hg).1
        omega
      obtain ⟨hq, hh, ht⟩ := trace_at (B := B) x w htag hg s
      obtain ⟨hb1, hb2, hb3⟩ := head_bounds (s := s) hN
      dsimp only
      rw [hq, ht, hh]
      refine ⟨fun hright => ?_, fun _ => by omega⟩
      by_cases hk : traceHead (a + m) zeros s = a + m + 1
      · have hs := hb3 hk
        have hr : marked x w zeros (a + m + 1) = none := by
          unfold marked
          rw [if_neg (show ¬ a + m + 1 = 8 + zeros by omega)]
          exact content_ge x w (by omega)
        rw [state_write hN hs, hk, tape_marked (by omega) (by omega), hr] at hright
        exact absurd hright (by decide)
      · unfold tapeLength pairLength
        omega

/-- The head stays in `[6, a+m+1]`, and only the marker and scratch cells ever
differ from `contentTape`. -/
theorem footprint {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (s : Nat) :
    let d := machine.run s (startConfig B x w)
    6 ≤ d.head.val ∧ d.head.val ≤ a + m + 1 ∧
      ∀ i : Fin (tapeLength (pairLength a m) B), i.val ≠ 8 + zeros →
        i.val ≠ a + m + 1 → d.tape i = FixedPairContentMarkerErase.contentTape B x w i := by
  have hN : 9 + zeros ≤ a + m := by
    have := ((FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 zeros hg).1
    omega
  obtain ⟨_, hh, ht⟩ := trace_at (B := B) x w htag hg s
  obtain ⟨hb1, hb2, _⟩ := head_bounds (s := s) hN
  refine ⟨by rw [hh]; exact hb1, by rw [hh]; exact hb2, fun i h1 h2 => ?_⟩
  rw [ht i]
  exact tapeAt_off x w h1 h2

private theorem same_of_at {n B B' : Nat} {c : Config stateCount n B}
    {c' : Config stateCount n B'} {q : Fin stateCount} {k : Nat} {T : Nat → Option Bool}
    (h : At c q k T) (h' : At c' q k T) :
    c.state = c'.state ∧ c.head.val = c'.head.val ∧
      ∀ (i : Fin (tapeLength n B)) (i' : Fin (tapeLength n B')), i.val = i'.val →
        c.tape i = c'.tape i' := by
  obtain ⟨hq, hh, ht⟩ := h
  obtain ⟨hq', hh', ht'⟩ := h'
  exact ⟨hq.trans hq'.symm, hh.trans hh'.symm, fun i i' hi => by rw [ht, ht', hi]⟩

/-- Control, numeric head, and equal-address tape cells agree across budgets at
every time, on every tagged input. -/
theorem budget_independence {a m : Nat} (B B' : Nat) (x : Bitstring a)
    (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true) (s : Nat) :
    (machine.run s (startConfig B x w)).state =
        (machine.run s (startConfig B' x w)).state ∧
    (machine.run s (startConfig B x w)).head.val =
        (machine.run s (startConfig B' x w)).head.val ∧
    ∀ (i : Fin (tapeLength (pairLength a m) B))
        (i' : Fin (tapeLength (pairLength a m) B')),
      i.val = i'.val →
      (machine.run s (startConfig B x w)).tape i =
        (machine.run s (startConfig B' x w)).tape i' := by
  cases hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) with
  | none => exact same_of_at (malformed_at x w htag hg s) (malformed_at x w htag hg s)
  | some zeros => exact same_of_at (trace_at x w htag hg s) (trace_at x w htag hg s)

/-- A failed gamma scan rejects after one step, at the dispatcher's head `a+m`,
with `contentTape` unchanged. -/
theorem malformed_exact {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = none)
    (s : Nat) (hs : 1 ≤ s) :
    let d := machine.run s (startConfig B x w)
    d.state = qReject ∧ d.head.val = a + m ∧
      d.tape = FixedPairContentMarkerErase.contentTape B x w := by
  obtain ⟨hq, hh, ht⟩ := malformed_at (B := B) x w htag hg s
  rw [if_neg (show ¬ s = 0 by omega)] at hq
  exact ⟨hq, hh, funext ht⟩

theorem malformed_at_deadline {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = none) :
    let d := machine.run (deadline (a + m)) (startConfig B x w)
    d.state = qReject ∧ d.head.val = a + m ∧
      d.tape = FixedPairContentMarkerErase.contentTape B x w :=
  malformed_exact x w htag hg _ (by
    have := (FixedContentTagGate.tag_contract (Fin.append x w)).2.2.2.2.2.2.2.2.2 htag
    unfold deadline
    omega)

end Pnp3.Complexity.Uniform.V1.FixedGammaTerminatorScratchBootstrap
