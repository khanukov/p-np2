import Complexity.Uniform.V1.FixedGammaTerminatorScratchBootstrap

/-!
# First gamma payload bit of the target scratch register (Part A G2p-b)

A fixed 18-state, 54-row machine whose start configuration retags the *actual*
G2p-a bootstrap configuration at the bootstrap deadline.  Only the control is
replaced; the gamma width, the payload bit, and every parser fact stay out of
the control.

Write `N = a + m`.  The target register holds `n + 1` most significant bit first
from scratch cell `N + 1`; the bootstrap wrote its leading `true` there and
halted on the physical terminator `8 + zeros`.  On a matching tag the run blanks
the terminator as a return marker, walks left over the gamma zeros to tag cell
`6`, and blanks cell `7` as an anchor.  Then:

* width zero: the cell after the anchor is the marker, so the machine restores
  the terminator and cell `7` and halts.  It reads no cell beyond `8` and needs
  no room past `N + 1`;
* positive width: it walks right to the marker and reads cell `9 + zeros`.  A
  physical `some b` is carried as `b` across the content to the blank boundary
  `N`; a blank there (`9 + zeros = N`) is the virtual zero and is carried as
  `false`.  The machine steps over the scratch `true` at `N + 1` without using
  it as source, writes the carried bit at `N + 2`, returns to the marker,
  restores the terminator, seeks the anchor, and restores cell `7`.  Cell
  `N + 2` must be allocated: `a + m + 2 < tapeLength (pairLength a m) B`, i.e.
  `0 < a + B`.  The positive-width theorems assume exactly this.

At the length-only deadline `3 * N` every successful run is in the absorbing
`qDone` at head `7`, on the bootstrap scratch tape (width zero) or on that tape
with the carried bit at `N + 2`.  A failed gamma scan rejects at the bootstrap
head `N` with `contentTape`.

`qDone` is an internal endpoint, not language acceptance.  Only the first
payload bit is copied; the remaining payload bits, the decrement to `n`, and
every pnp4 reader fact are outside this module.  This is uniform-machine
infrastructure, not P-vs-NP mainline progress.
-/

namespace Pnp3.Complexity.Uniform.V1.FixedGammaTargetFirstPayload

open PairEncoding

abbrev stateCount : Nat := 18

def qStart : Fin stateCount := ⟨0, by decide⟩
def qBack : Fin stateCount := ⟨1, by decide⟩
def qMarkSeven : Fin stateCount := ⟨2, by decide⟩
def qInspectEight : Fin stateCount := ⟨3, by decide⟩
def qSeekTerm : Fin stateCount := ⟨4, by decide⟩
def qReadPayload : Fin stateCount := ⟨5, by decide⟩
def qScanRight0 : Fin stateCount := ⟨6, by decide⟩
def qScanRight1 : Fin stateCount := ⟨7, by decide⟩
def qCrossScratch0 : Fin stateCount := ⟨8, by decide⟩
def qCrossScratch1 : Fin stateCount := ⟨9, by decide⟩
def qWrite0 : Fin stateCount := ⟨10, by decide⟩
def qWrite1 : Fin stateCount := ⟨11, by decide⟩
def qBackScratch : Fin stateCount := ⟨12, by decide⟩
def qCrossBoundary : Fin stateCount := ⟨13, by decide⟩
def qScanLeft : Fin stateCount := ⟨14, by decide⟩
def qSeekAnchor : Fin stateCount := ⟨15, by decide⟩
def qDone : Fin stateCount := ⟨16, by decide⟩
def qReject : Fin stateCount := ⟨17, by decide⟩

/-- The complete fixed 18-state, 54-row table. -/
def raw (q : Fin stateCount) (s : Option Bool) : Fin stateCount × Option Bool × Move :=
  match q.1 with
  | 0 => match s with
    | some true => (qBack, none, .left)
    | s => (qReject, s, .stay)
  | 1 => match s with
    | some false => (qBack, some false, .left)
    | some true => (qMarkSeven, some true, .right)
    | none => (qReject, none, .stay)
  | 2 => match s with
    | some false => (qInspectEight, none, .right)
    | s => (qReject, s, .stay)
  | 3 => match s with
    | none => (qSeekAnchor, some true, .left)
    | some false => (qSeekTerm, some false, .right)
    | some true => (qReject, some true, .stay)
  | 4 => match s with
    | some false => (qSeekTerm, some false, .right)
    | none => (qReadPayload, none, .right)
    | some true => (qReject, some true, .stay)
  | 5 => match s with
    | some false => (qScanRight0, some false, .right)
    | some true => (qScanRight1, some true, .right)
    | none => (qCrossScratch0, none, .right)
  | 6 => match s with
    | some b => (qScanRight0, some b, .right)
    | none => (qCrossScratch0, none, .right)
  | 7 => match s with
    | some b => (qScanRight1, some b, .right)
    | none => (qCrossScratch1, none, .right)
  | 8 => match s with
    | some true => (qWrite0, some true, .right)
    | s => (qReject, s, .stay)
  | 9 => match s with
    | some true => (qWrite1, some true, .right)
    | s => (qReject, s, .stay)
  | 10 => match s with
    | none => (qBackScratch, some false, .left)
    | s => (qReject, s, .stay)
  | 11 => match s with
    | none => (qBackScratch, some true, .left)
    | s => (qReject, s, .stay)
  | 12 => match s with
    | some true => (qCrossBoundary, some true, .left)
    | s => (qReject, s, .stay)
  | 13 => match s with
    | none => (qScanLeft, none, .left)
    | s => (qReject, s, .stay)
  | 14 => match s with
    | some b => (qScanLeft, some b, .left)
    | none => (qSeekAnchor, some true, .left)
  | 15 => match s with
    | some false => (qSeekAnchor, some false, .left)
    | none => (qDone, some false, .stay)
    | some true => (qReject, some true, .stay)
  | 16 => (qDone, s, .stay)
  | _ => (qReject, s, .stay)

def machine : UniformTM where
  stateCount := stateCount
  start := qStart
  accept := qDone
  reject := qReject
  accept_ne_reject := by decide
  rawStep := raw

/-- Honest input ABI: only the control of the actual bootstrap configuration is
replaced. -/
def retagBootstrap {N B : Nat}
    (c : Config FixedGammaTerminatorScratchBootstrap.stateCount N B) :
    Config stateCount N B := ⟨qStart, c.head, c.tape⟩

def startConfig {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) :
    Config stateCount (pairLength a m) B :=
  retagBootstrap (FixedGammaTerminatorScratchBootstrap.machine.run
    (FixedGammaTerminatorScratchBootstrap.deadline (a + m))
    (FixedGammaTerminatorScratchBootstrap.startConfig B x w))

/-- Public length-only deadline. -/
def deadline (N : Nat) : Nat := 3 * N

/-- The bootstrap scratch tape with bit `b` at the first payload cell `a + m + 2`. -/
def firstPayloadTape {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) (b : Bool) :
    Fin (tapeLength (pairLength a m) B) → Option Bool := fun i =>
  if i.val = a + m + 2 then some b else FixedGammaTerminatorScratchBootstrap.scratchTape B x w i

/-- Every row, pinned literally, with the resource counts. -/
theorem table_and_resource_pins :
    machine.step qStart none = (qReject, none, .stay) ∧
    machine.step qStart (some false) = (qReject, some false, .stay) ∧
    machine.step qStart (some true) = (qBack, none, .left) ∧
    machine.step qBack none = (qReject, none, .stay) ∧
    machine.step qBack (some false) = (qBack, some false, .left) ∧
    machine.step qBack (some true) = (qMarkSeven, some true, .right) ∧
    machine.step qMarkSeven none = (qReject, none, .stay) ∧
    machine.step qMarkSeven (some false) = (qInspectEight, none, .right) ∧
    machine.step qMarkSeven (some true) = (qReject, some true, .stay) ∧
    machine.step qInspectEight none = (qSeekAnchor, some true, .left) ∧
    machine.step qInspectEight (some false) = (qSeekTerm, some false, .right) ∧
    machine.step qInspectEight (some true) = (qReject, some true, .stay) ∧
    machine.step qSeekTerm none = (qReadPayload, none, .right) ∧
    machine.step qSeekTerm (some false) = (qSeekTerm, some false, .right) ∧
    machine.step qSeekTerm (some true) = (qReject, some true, .stay) ∧
    machine.step qReadPayload none = (qCrossScratch0, none, .right) ∧
    machine.step qReadPayload (some false) = (qScanRight0, some false, .right) ∧
    machine.step qReadPayload (some true) = (qScanRight1, some true, .right) ∧
    machine.step qScanRight0 none = (qCrossScratch0, none, .right) ∧
    machine.step qScanRight0 (some false) = (qScanRight0, some false, .right) ∧
    machine.step qScanRight0 (some true) = (qScanRight0, some true, .right) ∧
    machine.step qScanRight1 none = (qCrossScratch1, none, .right) ∧
    machine.step qScanRight1 (some false) = (qScanRight1, some false, .right) ∧
    machine.step qScanRight1 (some true) = (qScanRight1, some true, .right) ∧
    machine.step qCrossScratch0 none = (qReject, none, .stay) ∧
    machine.step qCrossScratch0 (some false) = (qReject, some false, .stay) ∧
    machine.step qCrossScratch0 (some true) = (qWrite0, some true, .right) ∧
    machine.step qCrossScratch1 none = (qReject, none, .stay) ∧
    machine.step qCrossScratch1 (some false) = (qReject, some false, .stay) ∧
    machine.step qCrossScratch1 (some true) = (qWrite1, some true, .right) ∧
    machine.step qWrite0 none = (qBackScratch, some false, .left) ∧
    machine.step qWrite0 (some false) = (qReject, some false, .stay) ∧
    machine.step qWrite0 (some true) = (qReject, some true, .stay) ∧
    machine.step qWrite1 none = (qBackScratch, some true, .left) ∧
    machine.step qWrite1 (some false) = (qReject, some false, .stay) ∧
    machine.step qWrite1 (some true) = (qReject, some true, .stay) ∧
    machine.step qBackScratch none = (qReject, none, .stay) ∧
    machine.step qBackScratch (some false) = (qReject, some false, .stay) ∧
    machine.step qBackScratch (some true) = (qCrossBoundary, some true, .left) ∧
    machine.step qCrossBoundary none = (qScanLeft, none, .left) ∧
    machine.step qCrossBoundary (some false) = (qReject, some false, .stay) ∧
    machine.step qCrossBoundary (some true) = (qReject, some true, .stay) ∧
    machine.step qScanLeft none = (qSeekAnchor, some true, .left) ∧
    machine.step qScanLeft (some false) = (qScanLeft, some false, .left) ∧
    machine.step qScanLeft (some true) = (qScanLeft, some true, .left) ∧
    machine.step qSeekAnchor none = (qDone, some false, .stay) ∧
    machine.step qSeekAnchor (some false) = (qSeekAnchor, some false, .left) ∧
    machine.step qSeekAnchor (some true) = (qReject, some true, .stay) ∧
    machine.step qDone none = (qDone, none, .stay) ∧
    machine.step qDone (some false) = (qDone, some false, .stay) ∧
    machine.step qDone (some true) = (qDone, some true, .stay) ∧
    machine.step qReject none = (qReject, none, .stay) ∧
    machine.step qReject (some false) = (qReject, some false, .stay) ∧
    machine.step qReject (some true) = (qReject, some true, .stay) ∧
    machine.stateCount = 18 ∧ machine.start = qStart ∧
    machine.accept = qDone ∧ machine.reject = qReject ∧
    qStart.val = 0 ∧ qBack.val = 1 ∧ qMarkSeven.val = 2 ∧ qInspectEight.val = 3 ∧
    qSeekTerm.val = 4 ∧ qReadPayload.val = 5 ∧ qScanRight0.val = 6 ∧
    qScanRight1.val = 7 ∧ qCrossScratch0.val = 8 ∧ qCrossScratch1.val = 9 ∧
    qWrite0.val = 10 ∧ qWrite1.val = 11 ∧ qBackScratch.val = 12 ∧
    qCrossBoundary.val = 13 ∧ qScanLeft.val = 14 ∧ qSeekAnchor.val = 15 ∧
    qDone.val = 16 ∧ qReject.val = 17 ∧
    Fintype.card (Fin machine.stateCount × Option Bool) = 54 := by
  repeat' apply And.intro
  all_goals rfl

theorem per_step_budget_independent : ∀ q s, machine.step q s = machine.rawStep q s := by
  intro q s
  fin_cases q <;> cases s with
  | none => rfl
  | some b => cases b <;> rfl

theorem endpoints_absorb {N B : Nat} (c : Config stateCount N B) :
    (c.state = qDone → ∀ n, machine.run n c = c) ∧
    (c.state = qReject → ∀ n, machine.run n c = c) :=
  ⟨fun h n => machine.run_accept c h n, fun h n => machine.run_reject c h n⟩

theorem handoff_exact {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let p := FixedGammaTerminatorScratchBootstrap.machine.run
      (FixedGammaTerminatorScratchBootstrap.deadline (a + m))
      (FixedGammaTerminatorScratchBootstrap.startConfig B x w)
    let c := startConfig B x w
    c = retagBootstrap p ∧ c.state = machine.start ∧ c.head = p.head ∧
      c.tape = p.tape :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The endpoint tape restores every source cell, keeps the boundary blank,
holds the leading `true` and the first payload bit, and is blank afterwards. -/
theorem firstPayloadTape_layout {a m B : Nat} (x : Bitstring a) (w : Bitstring m) (b : Bool)
    (hroom : a + m + 2 < tapeLength (pairLength a m) B) :
    (∀ j : Fin (a + m), firstPayloadTape B x w b
      ⟨j.val, by unfold tapeLength pairLength; omega⟩ = some (Fin.append x w j)) ∧
    firstPayloadTape B x w b ⟨a + m, by unfold tapeLength pairLength; omega⟩ = none ∧
    firstPayloadTape B x w b ⟨a + m + 1, by unfold tapeLength pairLength; omega⟩ =
      some true ∧
    firstPayloadTape B x w b ⟨a + m + 2, hroom⟩ = some b ∧
    ∀ i : Fin (tapeLength (pairLength a m) B), a + m + 2 < i.val →
      firstPayloadTape B x w b i = none := by
  obtain ⟨h1, h2, h3, h4⟩ := FixedGammaTerminatorScratchBootstrap.scratchTape_layout (B := B) x w
  refine ⟨fun j => ?_, ?_, ?_, ?_, fun i hi => ?_⟩ <;> unfold firstPayloadTape
  · rw [if_neg (show ¬ j.val = a + m + 2 by omega)]; exact h1 j
  · rw [if_neg (show ¬ a + m = a + m + 2 by omega)]; exact h2
  · rw [if_neg (show ¬ a + m + 1 = a + m + 2 by omega)]; exact h3
  · rw [if_pos rfl]
  · rw [if_neg (show ¬ i.val = a + m + 2 by omega)]; exact h4 i (by omega)

/-! ### Address-level execution invariant -/

private def content {a m : Nat} (x : Bitstring a) (w : Bitstring m) : Nat → Option Bool :=
  FixedContentTagGate.physicalSymbol (Fin.append x w)

private def scratch {a m : Nat} (x : Bitstring a) (w : Bitstring m) (k : Nat) :
    Option Bool :=
  if k = a + m + 1 then some true else content x w k

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

/-! ### Rows carrying the payload bit -/

private def scanState (c : Bool) : Fin stateCount := if c then qScanRight1 else qScanRight0
private def crossState (c : Bool) : Fin stateCount :=
  if c then qCrossScratch1 else qCrossScratch0
private def writeState (c : Bool) : Fin stateCount := if c then qWrite1 else qWrite0

private theorem row_read (b : Bool) :
    machine.step qReadPayload (some b) = (scanState b, some b, .right) := by
  cases b <;> rfl

private theorem row_scan (c b : Bool) :
    machine.step (scanState c) (some b) = (scanState c, some b, .right) := by
  cases c <;> cases b <;> rfl

private theorem row_scanEnd (c : Bool) :
    machine.step (scanState c) none = (crossState c, none, .right) := by
  cases c <;> rfl

private theorem row_cross (c : Bool) :
    machine.step (crossState c) (some true) = (writeState c, some true, .right) := by
  cases c <;> rfl

private theorem row_write (c : Bool) :
    machine.step (writeState c) none = (qBackScratch, some c, .left) := by
  cases c <;> rfl

private theorem row_scanLeft (b : Bool) :
    machine.step qScanLeft (some b) = (qScanLeft, some b, .left) := by
  cases b <;> rfl

/-! ### Budget-free schedules -/

/-- Control schedule of a positive-width run carrying bit `c`. -/
private def posState (N zeros : Nat) (c : Bool) (s : Nat) : Fin stateCount :=
  if s ≤ 4 + zeros then
    (if s = 0 then qStart else if s ≤ 2 + zeros then qBack
      else if s = 3 + zeros then qMarkSeven else qInspectEight)
  else if s ≤ N + zeros - 3 then
    (if s ≤ 4 + 2 * zeros then qSeekTerm else if s = 5 + 2 * zeros then qReadPayload
      else if s ≤ N + zeros - 4 then scanState c else crossState c)
  else if s ≤ N + zeros then
    (if s = N + zeros - 2 then writeState c else if s = N + zeros - 1 then qBackScratch
      else qCrossBoundary)
  else if s ≤ 2 * N - 8 then qScanLeft
  else if s ≤ 2 * N + zeros - 7 then qSeekAnchor
  else qDone

private def posHead (N zeros s : Nat) : Nat :=
  if s ≤ 2 + zeros then 8 + zeros - s
  else if s ≤ N + zeros - 2 then s + 4 - zeros
  else if s ≤ 2 * N + zeros - 7 then 2 * N + zeros - s
  else 7

/-- Tape of a positive-width run: the anchor blank at `7`, the marker blank at
`8 + zeros`, and the carried bit at `N + 2`, each over its time window. -/
private def posTape {a m : Nat} (x : Bitstring a) (w : Bitstring m) (zeros : Nat) (c : Bool)
    (s k : Nat) : Option Bool :=
  if k = 7 ∧ 4 + zeros ≤ s ∧ s ≤ 2 * (a + m) + zeros - 7 then none
  else if k = 8 + zeros ∧ 1 ≤ s ∧ s ≤ 2 * (a + m) - 8 then none
  else if k = a + m + 2 ∧ a + m + zeros - 1 ≤ s then some c
  else scratch x w k

private def zeroState (s : Nat) : Fin stateCount :=
  if s = 0 then qStart else if s ≤ 2 then qBack else if s = 3 then qMarkSeven
  else if s = 4 then qInspectEight else if s = 5 then qSeekAnchor else qDone

private def zeroHead (s : Nat) : Nat := if s ≤ 2 then 8 - s else if s = 4 then 8 else 7

private def zeroTape {a m : Nat} (x : Bitstring a) (w : Bitstring m) (s k : Nat) :
    Option Bool :=
  if k = 7 ∧ 4 ≤ s ∧ s ≤ 5 then none else if k = 8 ∧ 1 ≤ s ∧ s ≤ 4 then none
  else scratch x w k

/-! ### Traces -/

private theorem content_lt {a m : Nat} (x : Bitstring a) (w : Bitstring m) {k : Nat}
    (hk : k < a + m) : ∃ b, content x w k = some b :=
  ⟨Fin.append x w ⟨k, hk⟩, by
    unfold content FixedContentTagGate.physicalSymbol
    rw [dif_pos hk]⟩

private theorem content_ge {a m : Nat} (x : Bitstring a) (w : Bitstring m) {k : Nat}
    (hk : a + m ≤ k) : content x w k = none := by
  unfold content FixedContentTagGate.physicalSymbol
  rw [dif_neg (show ¬ k < a + m by omega)]

private theorem posTape_succ {a m : Nat} {x : Bitstring a} {w : Bitstring m} {zeros s : Nat}
    {c : Bool} (hN : 9 + zeros ≤ a + m)
    (h : s ≠ 0 ∧ s ≠ 3 + zeros ∧ s ≠ a + m + zeros - 2 ∧ s ≠ 2 * (a + m) - 8 ∧
      s ≠ 2 * (a + m) + zeros - 7) :
    posTape x w zeros c (s + 1) = posTape x w zeros c s := by
  funext k
  unfold posTape
  split_ifs <;> first | rfl | omega

private theorem posTape_content {a m : Nat} {x : Bitstring a} {w : Bitstring m}
    {zeros s k : Nat} {c : Bool}
    (h : (k ≠ 7 ∨ s < 4 + zeros ∨ 2 * (a + m) + zeros - 7 < s) ∧
      (k ≠ 8 + zeros ∨ s = 0 ∨ 2 * (a + m) - 8 < s) ∧ k ≠ a + m + 1 ∧
      (k ≠ a + m + 2 ∨ s + 1 < a + m + zeros)) :
    posTape x w zeros c s k = content x w k := by
  unfold posTape scratch
  split_ifs <;> first | rfl | omega

private theorem posTape_scratch {a m : Nat} {x : Bitstring a} {w : Bitstring m}
    {zeros s : Nat} {c : Bool} (hN : 9 + zeros ≤ a + m) :
    posTape x w zeros c s (a + m + 1) = some true := by
  unfold posTape scratch
  split_ifs <;> first | rfl | omega

private theorem zeroTape_content {a m : Nat} {x : Bitstring a} {w : Bitstring m} {s k : Nat}
    (h : (k ≠ 7 ∨ s < 4 ∨ 5 < s) ∧ (k ≠ 8 ∨ s = 0 ∨ 4 < s) ∧ k ≠ a + m + 1) :
    zeroTape x w s k = content x w k := by
  unfold zeroTape scratch
  split_ifs <;> first | rfl | omega

/-- Tag cells `6`, `7` and the gamma zeros, as used by both successful traces. -/
private theorem gamma_cells {a m zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros) :
    9 + zeros ≤ a + m ∧ content x w 6 = some true ∧ content x w (8 + zeros) = some true ∧
      ∀ i, 7 ≤ i → i < 8 + zeros → content x w i = some false := by
  obtain ⟨hlt, hterm, hzero⟩ :=
    (FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 zeros hg
  have hall := ((FixedContentTagGate.tag_contract (Fin.append x w)).2.2.2.2.2.2.2.2.1).1 htag
  have h6 := hall ⟨6, by decide⟩
  have h7 := hall ⟨7, by decide⟩
  refine ⟨by omega, h6, hterm, fun i h1 h2 => ?_⟩
  rcases Nat.lt_or_ge i 8 with h | h
  · rw [show i = 7 by omega]
    exact h7
  · have hi := hzero (i - 8) (by omega)
    rwa [show 8 + (i - 8) = i by omega] at hi

/-- The bit carried by a positive-width run: the physical payload bit, or the
virtual zero when the payload cell is the blank boundary. -/
private theorem carried_cases {a m zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (hN : 9 + zeros ≤ a + m) :
    content x w (9 + zeros) = some ((content x w (9 + zeros)).getD false) ∨
      (9 + zeros = a + m ∧ (content x w (9 + zeros)).getD false = false) := by
  unfold content FixedContentTagGate.physicalSymbol
  split
  · exact Or.inl rfl
  · exact Or.inr ⟨by omega, rfl⟩

private theorem start_at {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros) :
    At (startConfig B x w) qStart (8 + zeros) (scratch x w) := by
  obtain ⟨_, hh, ht⟩ := FixedGammaTerminatorScratchBootstrap.run_deadline (B := B) x w htag hg
  exact ⟨rfl, hh, fun i => congrFun ht i⟩

private theorem malformed_at {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = none) (s : Nat) :
    At (machine.run s (startConfig B x w)) (if s = 0 then qStart else qReject) (a + m)
      (content x w) := by
  induction s with
  | zero =>
      obtain ⟨_, hh, ht⟩ :=
        FixedGammaTerminatorScratchBootstrap.malformed_at_deadline (B := B) x w htag hg
      exact ⟨rfl, hh, fun i => congrFun ht i⟩
  | succ s ih =>
      rw [if_neg (show ¬ s + 1 = 0 by omega)]
      by_cases hs : s = 0
      · rw [if_pos hs] at ih
        exact stepAt_stay ih (content_ge x w le_rfl) rfl rfl (content_ge x w le_rfl)
          (fun _ _ => rfl)
      · rw [if_neg hs] at ih
        exact stepAt_stay ih rfl (machine.step_reject _) rfl rfl (fun _ _ => rfl)

private theorem zero_at {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some 0) (s : Nat) :
    At (machine.run s (startConfig B x w)) (zeroState s) (zeroHead s) (zeroTape x w s) := by
  obtain ⟨hN, h6, h8, hfalse⟩ := gamma_cells x w htag hg
  have h7 := hfalse 7 le_rfl (by omega)
  induction s with
  | zero =>
      obtain ⟨hq, hh, ht⟩ := start_at (B := B) x w htag hg
      exact ⟨hq, hh, fun i => (ht i).trans (by unfold zeroTape; split_ifs <;> first | rfl | omega)⟩
  | succ s ih =>
      rcases (show s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ 6 ≤ s by omega)
        with rfl | rfl | rfl | rfl | rfl | rfl | h <;>
        simp (disch := omega) only [zeroState, zeroHead, if_pos, if_neg, if_true] at ih ⊢
      · -- Blank the terminator at cell `8`.
        exact stepAt_left ih ((zeroTape_content (by omega)).trans h8) rfl rfl
          (by unfold zeroTape; split_ifs <;> first | rfl | omega)
          (fun i hi => by unfold zeroTape; split_ifs <;> first | rfl | omega)
      · exact stepAt_left ih ((zeroTape_content (by omega)).trans h7) rfl rfl
          ((zeroTape_content (by omega)).trans h7)
          (fun i hi => by unfold zeroTape; split_ifs <;> first | rfl | omega)
      · exact stepAt_right ih ((zeroTape_content (by omega)).trans h6) rfl rfl
          (by unfold tapeLength pairLength; omega) ((zeroTape_content (by omega)).trans h6)
          (fun i hi => by unfold zeroTape; split_ifs <;> first | rfl | omega)
      · -- Blank the anchor at cell `7`.
        exact stepAt_right ih ((zeroTape_content (by omega)).trans h7) rfl rfl
          (by unfold tapeLength pairLength; omega)
          (by unfold zeroTape; split_ifs <;> first | rfl | omega)
          (fun i hi => by unfold zeroTape; split_ifs <;> first | rfl | omega)
      · -- The marker follows the anchor: restore the terminator.
        exact stepAt_left ih (r := none) (by unfold zeroTape; split_ifs <;> first | rfl | omega)
          rfl rfl ((zeroTape_content (by omega)).trans h8)
          (fun i hi => by unfold zeroTape; split_ifs <;> first | rfl | omega)
      · -- Restore the anchor and halt.
        exact stepAt_stay ih (r := none) (by unfold zeroTape; split_ifs <;> first | rfl | omega)
          rfl rfl ((zeroTape_content (by omega)).trans h7)
          (fun i hi => by unfold zeroTape; split_ifs <;> first | rfl | omega)
      · rw [show zeroTape x w (s + 1) = zeroTape x w s by
          funext k; unfold zeroTape; split_ifs <;> first | rfl | omega]
        exact stepAt_stay ih rfl (machine.step_accept _) rfl rfl (fun _ _ => rfl)

/-- Content facts behind a positive-width run carrying bit `c`. -/
private def Cells {a m : Nat} (x : Bitstring a) (w : Bitstring m) (zeros : Nat) (c : Bool) :
    Prop :=
  9 + zeros ≤ a + m ∧ content x w 6 = some true ∧ content x w (8 + zeros) = some true ∧
    (∀ i, 7 ≤ i → i < 8 + zeros → content x w i = some false) ∧
    (content x w (9 + zeros) = some c ∨ (9 + zeros = a + m ∧ c = false))

private def PosAt {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) (zeros : Nat)
    (c : Bool) (s : Nat) : Prop :=
  At (machine.run s (startConfig B x w)) (posState (a + m) zeros c s)
    (posHead (a + m) zeros s) (posTape x w zeros c s)

/-- Marker, walk back to the tag, anchor, and walk right to the marker. -/
private theorem pos_step_seek {a m B zeros s : Nat} {x : Bitstring a} {w : Bitstring m}
    {c : Bool} (hcells : Cells x w zeros c) (hz : 0 < zeros) (hs : s ≤ 4 + 2 * zeros)
    (ih : PosAt B x w zeros c s) : PosAt B x w zeros c (s + 1) := by
  obtain ⟨hN, h6, hterm, hfalse, -⟩ := hcells
  unfold PosAt at ih ⊢
  have hL : a + m + 2 ≤ tapeLength (pairLength a m) B := by
    unfold tapeLength pairLength
    omega
  rcases (show s = 0 ∨ (1 ≤ s ∧ s ≤ 1 + zeros) ∨ s = 2 + zeros ∨ s = 3 + zeros ∨
      (4 + zeros ≤ s ∧ s ≤ 3 + 2 * zeros) ∨ s = 4 + 2 * zeros by omega)
    with h | h | h | h | h | h
  · -- Blank the terminator as the return marker.
    subst h
    simp (disch := omega) only [posState, posHead, if_pos, if_neg, if_true] at ih ⊢
    refine stepAt_left ih ((posTape_content (by omega)).trans hterm) rfl (by omega) ?_
      (fun i hi => ?_) <;> (unfold posTape; split_ifs <;> first | rfl | omega)
  · simp (disch := omega) only [posState, posHead, if_pos, if_neg] at ih ⊢
    rw [posTape_succ hN (by omega)]
    have hr : posTape x w zeros c s (8 + zeros - s) = some false :=
      (posTape_content (by omega)).trans (hfalse _ (by omega) (by omega))
    exact stepAt_left ih hr rfl (by omega) hr (fun _ _ => rfl)
  · simp (disch := omega) only [posState, posHead, if_pos, if_neg] at ih ⊢
    rw [posTape_succ hN (by omega)]
    have hr : posTape x w zeros c s (8 + zeros - s) = some true := by
      rw [posTape_content (by omega), show 8 + zeros - s = 6 by omega]
      exact h6
    exact stepAt_right ih hr rfl (by omega) (by omega) hr (fun _ _ => rfl)
  · -- Blank the anchor at cell `7`.
    simp (disch := omega) only [posState, posHead, if_pos, if_neg] at ih ⊢
    refine stepAt_right ih ((posTape_content (by omega)).trans
      (hfalse (s + 4 - zeros) (by omega) (by omega))) rfl (by omega) (by omega) ?_
      (fun i hi => ?_) <;> (unfold posTape; split_ifs <;> first | rfl | omega)
  · -- Walk right over the gamma zeros from cell `8`.
    rcases Nat.lt_or_ge s (5 + zeros) with h' | h' <;>
      (simp (disch := omega) only [posState, posHead, if_pos, if_neg] at ih ⊢
       rw [posTape_succ hN (by omega)]
       have hr : posTape x w zeros c s (s + 4 - zeros) = some false :=
         (posTape_content (by omega)).trans (hfalse _ (by omega) (by omega))
       exact stepAt_right ih hr rfl (by omega) (by omega) hr (fun _ _ => rfl))
  · -- Cross the marker onto the first payload cell.
    simp (disch := omega) only [posState, posHead, if_pos, if_neg] at ih ⊢
    rw [posTape_succ hN (by omega)]
    have hr : posTape x w zeros c s (s + 4 - zeros) = none := by
      unfold posTape; split_ifs <;> first | rfl | omega
    exact stepAt_right ih hr rfl (by omega) (by omega) hr (fun _ _ => rfl)

/-- Read the payload cell, carry the bit over the boundary and the leading
scratch bit, write it, and step back over the scratch bit to the boundary. -/
private theorem pos_step_carry {a m B zeros s : Nat} {x : Bitstring a} {w : Bitstring m}
    {c : Bool} (hcells : Cells x w zeros c) (hz : 0 < zeros)
    (hs : 5 + 2 * zeros ≤ s ∧ s < a + m + zeros)
    (hroom : a + m + 2 < tapeLength (pairLength a m) B)
    (ih : PosAt B x w zeros c s) : PosAt B x w zeros c (s + 1) := by
  obtain ⟨hN, -, -, -, hc⟩ := hcells
  unfold PosAt at ih ⊢
  have hL : a + m + 2 ≤ tapeLength (pairLength a m) B := by
    unfold tapeLength pairLength
    omega
  rcases (show s = 5 + 2 * zeros ∨ (6 + 2 * zeros ≤ s ∧ s ≤ a + m + zeros - 5) ∨
      (6 + 2 * zeros ≤ s ∧ s = a + m + zeros - 4) ∨ s = a + m + zeros - 3 ∨
      s = a + m + zeros - 2 ∨ s = a + m + zeros - 1 by omega)
    with h | h | h | h | h | h
  · rcases hc with hc | ⟨hv, rfl⟩
    · -- Physical payload bit.
      have hp : 9 + zeros < a + m := by
        by_contra hge; rw [content_ge x w (by omega)] at hc; cases hc
      simp (disch := omega) only [posState, posHead, if_pos, if_neg] at ih ⊢
      rw [posTape_succ hN (by omega)]
      have hr : posTape x w zeros c s (s + 4 - zeros) = some c := by
        rw [posTape_content (by omega), show s + 4 - zeros = 9 + zeros by omega]
        exact hc
      exact stepAt_right ih hr (row_read c) (by omega) (by omega) hr (fun _ _ => rfl)
    · -- Virtual payload bit: the blank boundary.
      simp (disch := omega) only [posState, posHead, if_pos, if_neg] at ih ⊢
      rw [posTape_succ hN (by omega)]
      have hr : posTape x w zeros false s (s + 4 - zeros) = none :=
        (posTape_content (by omega)).trans (content_ge x w (by omega))
      exact stepAt_right ih hr rfl (by omega) (by omega) hr (fun _ _ => rfl)
  · simp (disch := omega) only [posState, posHead, if_pos, if_neg] at ih ⊢
    rw [posTape_succ hN (by omega)]
    obtain ⟨b, hb⟩ := content_lt x w (k := s + 4 - zeros) (by omega)
    have hr : posTape x w zeros c s (s + 4 - zeros) = some b :=
      (posTape_content (by omega)).trans hb
    exact stepAt_right ih hr (row_scan c b) (by omega) (by omega) hr (fun _ _ => rfl)
  · simp (disch := omega) only [posState, posHead, if_pos, if_neg] at ih ⊢
    rw [posTape_succ hN (by omega)]
    have hr : posTape x w zeros c s (s + 4 - zeros) = none :=
      (posTape_content (by omega)).trans (content_ge x w (by omega))
    exact stepAt_right ih hr (row_scanEnd c) (by omega) (by omega) hr (fun _ _ => rfl)
  · -- Step over the leading scratch bit; the payload cell must be allocated.
    simp (disch := omega) only [posState, posHead, if_pos, if_neg] at ih ⊢
    rw [posTape_succ hN (by omega)]
    have hr : posTape x w zeros c s (s + 4 - zeros) = some true := by
      rw [show s + 4 - zeros = a + m + 1 by omega]
      exact posTape_scratch hN
    exact stepAt_right ih hr (row_cross c) (by omega) (by omega) hr (fun _ _ => rfl)
  · -- Write the carried bit at `N + 2`.
    simp (disch := omega) only [posState, posHead, if_pos, if_neg] at ih ⊢
    refine stepAt_left ih ((posTape_content (by omega)).trans (content_ge x w (by omega)))
      (row_write c) (by omega) ?_ (fun i hi => ?_) <;>
      (unfold posTape; split_ifs <;> first | rfl | omega)
  · simp (disch := omega) only [posState, posHead, if_pos, if_neg] at ih ⊢
    rw [posTape_succ hN (by omega)]
    have hr : posTape x w zeros c s (2 * (a + m) + zeros - s) = some true := by
      rw [show 2 * (a + m) + zeros - s = a + m + 1 by omega]
      exact posTape_scratch hN
    exact stepAt_left ih hr rfl (by omega) hr (fun _ _ => rfl)

/-- Cross the boundary, return to the marker, restore it, seek the anchor,
restore cell `7`, and halt. -/
private theorem pos_step_return {a m B zeros s : Nat} {x : Bitstring a} {w : Bitstring m}
    {c : Bool} (hcells : Cells x w zeros c) (hz : 0 < zeros) (hs : a + m + zeros ≤ s)
    (ih : PosAt B x w zeros c s) : PosAt B x w zeros c (s + 1) := by
  obtain ⟨hN, -, hterm, hfalse, -⟩ := hcells
  unfold PosAt at ih ⊢
  rcases (show s = a + m + zeros ∨ (a + m + zeros < s ∧ s ≤ 2 * (a + m) - 9) ∨
      s = 2 * (a + m) - 8 ∨ (2 * (a + m) - 8 < s ∧ s ≤ 2 * (a + m) + zeros - 8) ∨
      s = 2 * (a + m) + zeros - 7 ∨ 2 * (a + m) + zeros - 7 < s by omega)
    with h | h | h | h | h | h
  · simp (disch := omega) only [posState, posHead, if_pos, if_neg] at ih ⊢
    rw [posTape_succ hN (by omega)]
    have hr : posTape x w zeros c s (2 * (a + m) + zeros - s) = none :=
      (posTape_content (by omega)).trans (content_ge x w (by omega))
    exact stepAt_left ih hr rfl (by omega) hr (fun _ _ => rfl)
  · simp (disch := omega) only [posState, posHead, if_pos, if_neg] at ih ⊢
    rw [posTape_succ hN (by omega)]
    obtain ⟨b, hb⟩ := content_lt x w (k := 2 * (a + m) + zeros - s) (by omega)
    have hr : posTape x w zeros c s (2 * (a + m) + zeros - s) = some b :=
      (posTape_content (by omega)).trans hb
    exact stepAt_left ih hr (row_scanLeft b) (by omega) hr (fun _ _ => rfl)
  · -- Restore the terminator.
    simp (disch := omega) only [posState, posHead, if_pos, if_neg] at ih ⊢
    refine stepAt_left ih (r := none) (by unfold posTape; split_ifs <;> first | rfl | omega)
      rfl (by omega) ?_ (fun i hi => by unfold posTape; split_ifs <;> first | rfl | omega)
    rw [posTape_content (by omega), show 2 * (a + m) + zeros - s = 8 + zeros by omega]
    exact hterm
  · simp (disch := omega) only [posState, posHead, if_pos, if_neg] at ih ⊢
    rw [posTape_succ hN (by omega)]
    have hr : posTape x w zeros c s (2 * (a + m) + zeros - s) = some false :=
      (posTape_content (by omega)).trans (hfalse _ (by omega) (by omega))
    exact stepAt_left ih hr rfl (by omega) hr (fun _ _ => rfl)
  · -- Restore the anchor and halt.
    simp (disch := omega) only [posState, posHead, if_pos, if_neg] at ih ⊢
    refine stepAt_stay ih (r := none) (by unfold posTape; split_ifs <;> first | rfl | omega)
      rfl (by omega) ?_ (fun i hi => by unfold posTape; split_ifs <;> first | rfl | omega)
    rw [posTape_content (by omega), show 2 * (a + m) + zeros - s = 7 by omega]
    exact hfalse 7 le_rfl (by omega)
  · simp (disch := omega) only [posState, posHead, if_pos, if_neg] at ih ⊢
    rw [posTape_succ hN (by omega)]
    exact stepAt_stay ih rfl (machine.step_accept _) rfl rfl (fun _ _ => rfl)

private theorem pos_at {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m) {c : Bool}
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hz : 0 < zeros)
    (hc : content x w (9 + zeros) = some c ∨ (9 + zeros = a + m ∧ c = false))
    (hroom : a + m + 2 < tapeLength (pairLength a m) B) (s : Nat) : PosAt B x w zeros c s := by
  obtain ⟨hN, h6, hterm, hfalse⟩ := gamma_cells x w htag hg
  have hcells : Cells x w zeros c := ⟨hN, h6, hterm, hfalse, hc⟩
  induction s with
  | zero =>
      obtain ⟨hq, hh, ht⟩ := start_at (B := B) x w htag hg
      refine ⟨hq.trans ?_, hh.trans ?_, fun i => (ht i).trans ?_⟩
      · simp (disch := omega) only [posState, if_pos, if_true]
      · unfold posHead
        split_ifs <;> omega
      · unfold posTape
        split_ifs <;> first | rfl | omega
  | succ s ih =>
      rcases (show s ≤ 4 + 2 * zeros ∨ (5 + 2 * zeros ≤ s ∧ s < a + m + zeros) ∨
          a + m + zeros ≤ s by omega) with h | h | h
      · exact pos_step_seek hcells hz h ih
      · exact pos_step_carry hcells hz h hroom ih
      · exact pos_step_return hcells hz h ih

/-! ### Public execution theorems -/

/-- A failed gamma scan ends in `qReject` at the bootstrap head `a + m`, with
`contentTape` unchanged.  No workspace premise is needed. -/
theorem malformed_at_deadline {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = none) :
    let d := machine.run (deadline (a + m)) (startConfig B x w)
    d.state = qReject ∧ d.head.val = a + m ∧
      d.tape = FixedPairContentMarkerErase.contentTape B x w := by
  have h8 := (FixedContentTagGate.tag_contract (Fin.append x w)).2.2.2.2.2.2.2.2.2 htag
  obtain ⟨hq, hh, ht⟩ := malformed_at (B := B) x w htag hg (deadline (a + m))
  rw [if_neg (show ¬ deadline (a + m) = 0 by unfold deadline; omega)] at hq
  exact ⟨hq, hh, funext ht⟩

/-- Width zero halts at head `7` on the unchanged bootstrap scratch tape, with no
room premise; `footprint` keeps this run within cells `[6, 8]`. -/
theorem zero_width_at_deadline {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some 0) :
    let d := machine.run (deadline (a + m)) (startConfig B x w)
    d.state = qDone ∧ d.head.val = 7 ∧
      d.tape = FixedGammaTerminatorScratchBootstrap.scratchTape B x w := by
  obtain ⟨hN, -⟩ := gamma_cells x w htag hg
  obtain ⟨hq, hh, ht⟩ := zero_at (B := B) x w htag hg (deadline (a + m))
  refine ⟨hq.trans ?_, hh.trans ?_, funext fun i => (ht i).trans ?_⟩
  · unfold zeroState deadline
    split_ifs <;> first | rfl | omega
  · unfold zeroHead deadline
    split_ifs <;> omega
  · unfold zeroTape scratch FixedGammaTerminatorScratchBootstrap.scratchTape deadline
    split_ifs <;> first | rfl | omega

/-- Positive width with an allocated first payload cell halts at head `7` with the
carried bit at `a + m + 2`: the physical payload bit, or `false` when the
payload cell is the blank boundary. -/
theorem first_payload_at_deadline {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzeros : 0 < zeros) (hroom : a + m + 2 < tapeLength (pairLength a m) B) :
    let d := machine.run (deadline (a + m)) (startConfig B x w)
    d.state = qDone ∧ d.head.val = 7 ∧
      d.tape = firstPayloadTape B x w
        ((FixedContentTagGate.physicalSymbol (Fin.append x w) (9 + zeros)).getD false) := by
  obtain ⟨hN, -⟩ := gamma_cells x w htag hg
  obtain ⟨hq, hh, ht⟩ :=
    pos_at (B := B) x w htag hg hzeros (carried_cases x w hN) hroom (deadline (a + m))
  refine ⟨hq.trans ?_, hh.trans ?_, funext fun i => (ht i).trans ?_⟩
  · simp (disch := omega) only [posState, deadline, if_pos, if_neg]
  · unfold posHead deadline
    split_ifs <;> omega
  · unfold posTape scratch firstPayloadTape FixedGammaTerminatorScratchBootstrap.scratchTape
      deadline
    split_ifs <;> first | rfl | omega

/-- A physical first payload bit `b` is copied to `a + m + 2`. -/
theorem first_physical_at_deadline {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (b : Bool) (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzeros : 0 < zeros)
    (hread : FixedContentTagGate.physicalSymbol (Fin.append x w) (9 + zeros) = some b)
    (hroom : a + m + 2 < tapeLength (pairLength a m) B) :
    let d := machine.run (deadline (a + m)) (startConfig B x w)
    d.state = qDone ∧ d.head.val = 7 ∧ d.tape = firstPayloadTape B x w b := by
  have h := first_payload_at_deadline (B := B) x w htag hg hzeros hroom
  rw [hread] at h
  exact h

/-- When the first payload cell is the blank boundary `a + m`, the virtual zero is
written at `a + m + 2`; the leading scratch `true` at `a + m + 1` is not taken as
the source bit. -/
theorem first_virtual_at_deadline {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzeros : 0 < zeros) (hvirtual : 9 + zeros = a + m)
    (hroom : a + m + 2 < tapeLength (pairLength a m) B) :
    let d := machine.run (deadline (a + m)) (startConfig B x w)
    d.state = qDone ∧ d.head.val = 7 ∧ d.tape = firstPayloadTape B x w false := by
  have h := first_payload_at_deadline (B := B) x w htag hg hzeros hroom
  rw [show FixedContentTagGate.physicalSymbol (Fin.append x w) (9 + zeros) = none from
    content_ge x w (by omega)] at h
  exact h

/-- On every tagged input, no transition at any time clamps at either end of the
tape, provided the first payload cell is allocated whenever the gamma width is
positive.  Malformed and zero-width inputs need no premise. -/
theorem no_boundary_clamp {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hroom : ∀ zeros, FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros →
      0 < zeros → a + m + 2 < tapeLength (pairLength a m) B) (s : Nat) :
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
      obtain ⟨hN, -⟩ := gamma_cells x w htag hg
      have hL : a + m + 2 ≤ tapeLength (pairLength a m) B := by
        unfold tapeLength pairLength
        omega
      rcases Nat.eq_zero_or_pos zeros with rfl | hz
      · obtain ⟨-, hh, -⟩ := zero_at (B := B) x w htag hg s
        have hb : 6 ≤ zeroHead s ∧ zeroHead s ≤ 8 := by
          unfold zeroHead
          split_ifs <;> omega
        dsimp only
        rw [hh]
        exact ⟨fun _ => by omega, fun _ => by omega⟩
      · obtain ⟨hq, hh, ht⟩ :=
          pos_at (B := B) x w htag hg hz (carried_cases x w hN) (hroom zeros hg hz) s
        have hb : 6 ≤ posHead (a + m) zeros s ∧ posHead (a + m) zeros s ≤ a + m + 2 ∧
            (posHead (a + m) zeros s = a + m + 2 → s = a + m + zeros - 2) := by
          unfold posHead
          split_ifs <;> omega
        dsimp only
        rw [hq, ht, hh]
        refine ⟨fun hright => ?_, fun _ => by omega⟩
        by_cases hk : posHead (a + m) zeros s = a + m + 2
        · have hs := hb.2.2 hk
          have hr : posTape x w zeros ((content x w (9 + zeros)).getD false) s (a + m + 2) =
              none := (posTape_content (by omega)).trans (content_ge x w (by omega))
          simp (disch := omega) only [posState, if_pos, if_neg] at hright
          rw [hk, hr, row_write] at hright
          cases hright
        · have := hroom zeros hg hz
          omega

/-- On a decoded width the head stays in `[6, 8]` for width zero and in
`[6, a+m+2]` otherwise, and only the anchor, the marker, and the two scratch cells
ever differ from `contentTape`. -/
theorem footprint {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hroom : 0 < zeros → a + m + 2 < tapeLength (pairLength a m) B) (s : Nat) :
    let d := machine.run s (startConfig B x w)
    6 ≤ d.head.val ∧ d.head.val ≤ (if zeros = 0 then 8 else a + m + 2) ∧
      ∀ i : Fin (tapeLength (pairLength a m) B), i.val ≠ 7 → i.val ≠ 8 + zeros →
        i.val ≠ a + m + 1 → i.val ≠ a + m + 2 →
          d.tape i = FixedPairContentMarkerErase.contentTape B x w i := by
  obtain ⟨hN, -⟩ := gamma_cells x w htag hg
  rcases Nat.eq_zero_or_pos zeros with rfl | hz
  · obtain ⟨-, hh, ht⟩ := zero_at (B := B) x w htag hg s
    have hb : 6 ≤ zeroHead s ∧ zeroHead s ≤ 8 := by
      unfold zeroHead
      split_ifs <;> omega
    refine ⟨by rw [hh]; omega, by rw [hh, if_pos rfl]; omega,
      fun i h1 h2 h3 h4 => (ht i).trans ?_⟩
    unfold zeroTape scratch
    split_ifs <;> first | rfl | omega
  · obtain ⟨-, hh, ht⟩ := pos_at (B := B) x w htag hg hz (carried_cases x w hN) (hroom hz) s
    have hb : 6 ≤ posHead (a + m) zeros s ∧ posHead (a + m) zeros s ≤ a + m + 2 := by
      unfold posHead
      split_ifs <;> omega
    refine ⟨by rw [hh]; omega, by rw [hh, if_neg (by omega)]; omega,
      fun i h1 h2 h3 h4 => (ht i).trans ?_⟩
    unfold posTape scratch
    split_ifs <;> first | rfl | omega

private theorem same_of_at {n B B' : Nat} {c : Config stateCount n B}
    {c' : Config stateCount n B'} {q : Fin stateCount} {k : Nat} {T : Nat → Option Bool}
    (h : At c q k T) (h' : At c' q k T) :
    c.state = c'.state ∧ c.head.val = c'.head.val ∧
      ∀ (i : Fin (tapeLength n B)) (i' : Fin (tapeLength n B')), i.val = i'.val →
        c.tape i = c'.tape i' := by
  obtain ⟨hq, hh, ht⟩ := h
  obtain ⟨hq', hh', ht'⟩ := h'
  exact ⟨hq.trans hq'.symm, hh.trans hh'.symm, fun i i' hi => by rw [ht, ht', hi]⟩

/-- Control, numeric head, and equal-address tape cells agree across two budgets
at every time, on every tagged input, when both budgets allocate the first
payload cell for positive widths. -/
theorem budget_independence {a m : Nat} (B B' : Nat) (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hroom : ∀ zeros, FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros →
      0 < zeros → a + m + 2 < tapeLength (pairLength a m) B ∧
        a + m + 2 < tapeLength (pairLength a m) B') (s : Nat) :
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
  | some zeros =>
      obtain ⟨hN, -⟩ := gamma_cells x w htag hg
      rcases Nat.eq_zero_or_pos zeros with rfl | hz
      · exact same_of_at (zero_at x w htag hg s) (zero_at x w htag hg s)
      · exact same_of_at (pos_at x w htag hg hz (carried_cases x w hN) (hroom zeros hg hz).1 s)
          (pos_at x w htag hg hz (carried_cases x w hN) (hroom zeros hg hz).2 s)

end Pnp3.Complexity.Uniform.V1.FixedGammaTargetFirstPayload
