import Complexity.Uniform.V1.FixedContentGammaAnchor
import Mathlib.Data.Fintype.Card

/-!
# Fixed gamma-payload cursor core (Part A G2b)

This infrastructure slice executes only the zero-width case and the first
round of the in-place rolling-hole representation.  It starts from the actual
successful G2a tape: cell 7 is blank and the head is on the gamma terminator.
For a nonempty zero run it blanks cell 8, scans right to the terminator, and
opens a cursor at the first payload cell.  A false physical bit is carried in
finite control as the next-round handoff.  A true bit or the first virtual
blank enters a distinct cleanup mode; this file pins those transition rows but
does not yet prove their general completion from the real handoff.  No theorem
in this file iterates the representation or identifies semantic acceptance.
-/

namespace Pnp3.Complexity.Uniform.V1.FixedGammaPayloadCursorCore

open PairEncoding

abbrev stateCount : Nat := 14
def qStart : Fin stateCount := ⟨0, by decide⟩
def qBackFirst : Fin stateCount := ⟨1, by decide⟩
def qBackSeen : Fin stateCount := ⟨2, by decide⟩
def qSpend : Fin stateCount := ⟨3, by decide⟩
def qSeekTerm : Fin stateCount := ⟨4, by decide⟩
def qRead : Fin stateCount := ⟨5, by decide⟩
def qNextFalse : Fin stateCount := ⟨6, by decide⟩
def qRestoreOne : Fin stateCount := ⟨7, by decide⟩
def qRestoreVirtual : Fin stateCount := ⟨8, by decide⟩
def qFillOne : Fin stateCount := ⟨9, by decide⟩
def qFillVirtual : Fin stateCount := ⟨10, by decide⟩
def qOne : Fin stateCount := ⟨11, by decide⟩
def qVirtual : Fin stateCount := ⟨12, by decide⟩
def qReject : Fin stateCount := ⟨13, by decide⟩

private def raw (q : Fin stateCount) (s : Option Bool) :
    Fin stateCount × Option Bool × Move :=
  match q.1 with
  | 0 => match s with
    | some true => (qBackFirst, some true, .left)
    | s => (qReject, s, .stay)
  | 1 => match s with
    | some false => (qBackSeen, some false, .left)
    | none => (qVirtual, some false, .stay)
    | s => (qReject, s, .stay)
  | 2 => match s with
    | some false => (qBackSeen, some false, .left)
    | none => (qSpend, none, .right)
    | s => (qReject, s, .stay)
  | 3 => match s with
    | some false => (qSeekTerm, none, .right)
    | s => (qReject, s, .stay)
  | 4 => match s with
    | some false => (qSeekTerm, some false, .right)
    | some true => (qRead, some true, .right)
    | none => (qReject, none, .stay)
  | 5 => match s with
    | some false => (qNextFalse, none, .stay)
    | some true => (qRestoreOne, some true, .left)
    | none => (qRestoreVirtual, none, .left)
  | 6 => (qNextFalse, s, .stay)
  | 7 => match s with
    | none => (qFillOne, some false, .left)
    | s => (qRestoreOne, s, .left)
  | 8 => match s with
    | none => (qFillVirtual, some false, .left)
    | s => (qRestoreVirtual, s, .left)
  | 9 => match s with
    | none => (qOne, some false, .left)
    | s => (qReject, s, .stay)
  | 10 => match s with
    | none => (qVirtual, some false, .left)
    | s => (qReject, s, .stay)
  | 11 => (qOne, s, .stay)
  | 12 => (qVirtual, s, .stay)
  | _ => (qReject, s, .stay)

def machine : UniformTM where
  stateCount := stateCount
  start := qStart
  accept := qOne
  reject := qReject
  accept_ne_reject := by decide
  rawStep := raw

private theorem start_true_action : machine.step qStart (some true) =
    (qBackFirst, some true, .left) := by decide
private theorem backFirst_none_action : machine.step qBackFirst none =
    (qVirtual, some false, .stay) := by decide
private theorem read_false_action : machine.step qRead (some false) =
    (qNextFalse, none, .stay) := by decide
private theorem read_true_action : machine.step qRead (some true) =
    (qRestoreOne, some true, .left) := by decide
private theorem read_none_action : machine.step qRead none =
    (qRestoreVirtual, none, .left) := by decide

private theorem backFirst_false_action : machine.step qBackFirst (some false) =
    (qBackSeen, some false, .left) := by decide
private theorem backSeen_false_action : machine.step qBackSeen (some false) =
    (qBackSeen, some false, .left) := by decide
private theorem backSeen_none_action : machine.step qBackSeen none =
    (qSpend, none, .right) := by decide
private theorem spend_false_action : machine.step qSpend (some false) =
    (qSeekTerm, none, .right) := by decide
private theorem seek_false_action : machine.step qSeekTerm (some false) =
    (qSeekTerm, some false, .right) := by decide
private theorem seek_true_action : machine.step qSeekTerm (some true) =
    (qRead, some true, .right) := by decide
private theorem restoreOne_none_action : machine.step qRestoreOne none =
    (qFillOne, some false, .left) := by decide
private theorem restoreVirtual_none_action : machine.step qRestoreVirtual none =
    (qFillVirtual, some false, .left) := by decide
private theorem fillOne_none_action : machine.step qFillOne none =
    (qOne, some false, .left) := by decide
private theorem fillVirtual_none_action : machine.step qFillVirtual none =
    (qVirtual, some false, .left) := by decide

def retag {N B : Nat} (c : Config FixedContentGammaAnchor.stateCount N B) :
    Config stateCount N B := ⟨qStart, c.head, c.tape⟩

def startConfig {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) :
    Config stateCount (pairLength a m) B :=
  retag (FixedContentGammaAnchor.finalConfig B x w)

/-- Full public table, including the absorbing public accept/reject rows. -/
theorem table_and_resource_pins :
    (∀ s, machine.step qStart s = match s with
      | some true => (qBackFirst, some true, .left)
      | some false => (qReject, some false, .stay)
      | none => (qReject, none, .stay)) ∧
    (∀ s, machine.step qBackFirst s = match s with
      | some false => (qBackSeen, some false, .left)
      | none => (qVirtual, some false, .stay)
      | some true => (qReject, some true, .stay)) ∧
    (∀ s, machine.step qBackSeen s = match s with
      | some false => (qBackSeen, some false, .left)
      | none => (qSpend, none, .right)
      | some true => (qReject, some true, .stay)) ∧
    (∀ s, machine.step qSpend s = match s with
      | some false => (qSeekTerm, none, .right)
      | some true => (qReject, some true, .stay)
      | none => (qReject, none, .stay)) ∧
    (∀ s, machine.step qSeekTerm s = match s with
      | some false => (qSeekTerm, some false, .right)
      | some true => (qRead, some true, .right)
      | none => (qReject, none, .stay)) ∧
    (∀ s, machine.step qRead s = match s with
      | some false => (qNextFalse, none, .stay)
      | some true => (qRestoreOne, some true, .left)
      | none => (qRestoreVirtual, none, .left)) ∧
    (∀ s, machine.step qNextFalse s = (qNextFalse, s, .stay)) ∧
    (∀ s, machine.step qRestoreOne s = match s with
      | none => (qFillOne, some false, .left)
      | some b => (qRestoreOne, some b, .left)) ∧
    (∀ s, machine.step qRestoreVirtual s = match s with
      | none => (qFillVirtual, some false, .left)
      | some b => (qRestoreVirtual, some b, .left)) ∧
    (∀ s, machine.step qFillOne s = match s with
      | none => (qOne, some false, .left)
      | some b => (qReject, some b, .stay)) ∧
    (∀ s, machine.step qFillVirtual s = match s with
      | none => (qVirtual, some false, .left)
      | some b => (qReject, some b, .stay)) ∧
    (∀ s, machine.step qOne s = (qOne, s, .stay)) ∧
    (∀ s, machine.step qVirtual s = (qVirtual, s, .stay)) ∧
    (∀ s, machine.step qReject s = (qReject, s, .stay)) ∧
    machine.stateCount = 14 ∧ machine.start = qStart ∧
    machine.accept = qOne ∧ machine.reject = qReject ∧
    Fintype.card (Fin machine.stateCount × Option Bool) = 42 := by
  refine ⟨fun s => by cases s with | none => decide | some b => cases b <;> decide,
    fun s => by cases s with | none => decide | some b => cases b <;> decide,
    fun s => by cases s with | none => decide | some b => cases b <;> decide,
    fun s => by cases s with | none => decide | some b => cases b <;> decide,
    fun s => by cases s with | none => decide | some b => cases b <;> decide,
    fun s => by cases s with | none => decide | some b => cases b <;> decide,
    fun s => by cases s with | none => decide | some b => cases b <;> decide,
    fun s => by cases s with | none => decide | some b => cases b <;> decide,
    fun s => by cases s with | none => decide | some b => cases b <;> decide,
    fun s => by cases s with | none => decide | some b => cases b <;> decide,
    fun s => by cases s with | none => decide | some b => cases b <;> decide,
    fun s => by cases s with | none => decide | some b => cases b <;> decide,
    fun s => by cases s with | none => decide | some b => cases b <;> decide,
    fun s => by cases s with | none => decide | some b => cases b <;> decide,
    rfl, rfl, rfl, rfl, by decide⟩

theorem handoff_exact {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true) :
    let p := FixedContentGammaAnchor.machine.run
      (FixedContentGammaAnchor.deadline a m)
      (FixedContentGammaAnchor.startConfig B x w)
    let c := startConfig B x w
    p = FixedContentGammaAnchor.finalConfig B x w ∧ c = retag p ∧
    c.state = machine.start ∧ c.head = p.head ∧ c.tape = p.tape := by
  dsimp
  rw [FixedContentGammaAnchor.run_deadline x w htag]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem successful_handoff_exact {a m B zeros : Nat}
    (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros) :
    let p := FixedContentGammaAnchor.machine.run
      (FixedContentGammaAnchor.deadline a m)
      (FixedContentGammaAnchor.startConfig B x w)
    let c := startConfig B x w
    p.state = FixedContentGammaAnchor.machine.accept ∧
    p.head.val = 8 + zeros ∧ p.tape = FixedContentGammaAnchor.markedTape B x w ∧
    c = retag p := by
  dsimp
  rw [FixedContentGammaAnchor.run_deadline x w htag]
  have hs := ((FixedContentGammaTerminator.gamma_contract _).1 zeros hg).1
  simp [FixedContentGammaAnchor.finalConfig, hg,
    FixedContentGammaTerminator.terminalIndex, Nat.min_eq_left (Nat.le_of_lt hs),
    FixedContentGammaAnchor.machine, startConfig]

private theorem config_ext {N B : Nat} {c d : Config stateCount N B}
    (hs : c.state = d.state) (hh : c.head = d.head) (ht : c.tape = d.tape) : c = d := by
  cases c; cases d; cases hs; cases hh; cases ht; rfl

private theorem step_eq {N B : Nat} (c : Config stateCount N B)
    (q' : Fin stateCount) (s' : Option Bool) (mv : Move)
    (h : machine.step c.state (c.tape c.head) = (q', s', mv)) :
    machine.stepConfig c =
      ⟨q', moveHead c.head mv, fun i => if i = c.head then s' else c.tape i⟩ := by
  apply config_ext
  · change (machine.step c.state (c.tape c.head)).1 = q'; rw [h]
  · change moveHead c.head (machine.step c.state (c.tape c.head)).2.2 = _; rw [h]
  · funext i
    change (if i = c.head then (machine.step c.state (c.tape c.head)).2.1 else c.tape i) = _
    rw [h]

/-- Canonical tape after the first physical-false branch: the G2a marker,
cell 8, and the first payload cell are holes.  The last hole's `false` value is
carried by `qNextFalse`; neither `zeros` nor the payload is in the start state. -/
def nextTape {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m)
    (zeros : Nat) : Fin (tapeLength (pairLength a m) B) → Option Bool := fun i =>
  if i.val = 7 ∨ i.val = 8 ∨ i.val = 9 + zeros then none
  else FixedPairContentMarkerErase.contentTape B x w i

def NextInvariant {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m)
    (zeros : Nat) (c : Config stateCount (pairLength a m) B) : Prop :=
  c.state = qNextFalse ∧ c.head.val = 9 + zeros ∧ c.tape = nextTape B x w zeros

private def openedTape {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) :=
  fun i : Fin (tapeLength (pairLength a m) B) =>
    if i.val = 7 ∨ i.val = 8 then none
    else FixedPairContentMarkerErase.contentTape B x w i

private def cursorConfig {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m)
    (q : Fin stateCount) (j : Nat) (hj : j < tapeLength (pairLength a m) B)
    (t := openedTape B x w) : Config stateCount (pairLength a m) B :=
  ⟨q, ⟨j, hj⟩, t⟩

private theorem content_at {a m B j : Nat} (x : Bitstring a) (w : Bitstring m)
    (hj : j < a + m) :
    FixedPairContentMarkerErase.contentTape B x w
      ⟨j, by unfold tapeLength pairLength; omega⟩ = some ((Fin.append x w) ⟨j, hj⟩) := by
  simp [FixedPairContentMarkerErase.contentTape, hj]

private theorem step_cursor_keep {a m B j : Nat} (x : Bitstring a) (w : Bitstring m)
    (q q' : Fin stateCount) (hj : j < tapeLength (pairLength a m) B) (mv : Move)
    (h : machine.step q (openedTape B x w ⟨j, hj⟩) =
      (q', openedTape B x w ⟨j, hj⟩, mv)) :
    machine.stepConfig (cursorConfig B x w q j hj) =
      ⟨q', moveHead ⟨j, hj⟩ mv, openedTape B x w⟩ := by
  rw [step_eq _ q' (openedTape B x w ⟨j, hj⟩) mv h]
  apply config_ext <;> try rfl
  funext i
  by_cases hi : i = ⟨j, hj⟩ <;> simp [cursorConfig, hi]

/-- For a nonempty gamma run, the first payload read is reached from the actual
G2a handoff.  Both marker cells are holes, while every other cell is still the
literal predecessor `contentTape`. -/
theorem first_read_reachable {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzero : 0 < zeros) :
    let c := machine.run (2 * zeros + 3) (startConfig B x w)
    c.state = qRead ∧ c.head.val = 9 + zeros ∧
      c.tape = openedTape B x w := by
  rcases (FixedContentGammaTerminator.gamma_contract _).1 zeros hg with ⟨hlt, ht, hz⟩
  have htermBit : (Fin.append x w) ⟨8 + zeros, hlt⟩ = true := by
    simpa [FixedContentTagGate.physicalSymbol, hlt] using ht
  have htaglen : 8 ≤ a + m := by
    rcases FixedContentTagGate.tag_contract (Fin.append x w) with
      ⟨_, _, _, _, _, _, _, _, _, hlen⟩
    exact hlen htag
  let marked := FixedContentGammaAnchor.markedTape B x w
  have hmarked (j : Nat) (hj : j < a + m) (hj7 : j ≠ 7) :
      marked ⟨j, by unfold tapeLength pairLength; omega⟩ =
        some ((Fin.append x w) ⟨j, hj⟩) := by
    simp [marked, FixedContentGammaAnchor.markedTape, hj7,
      FixedPairContentMarkerErase.contentTape, hj]
  have hstart : startConfig B x w =
      (⟨qStart, ⟨8 + zeros, by unfold tapeLength pairLength; omega⟩, marked⟩ :
        Config stateCount (pairLength a m) B) := by
    apply config_ext
    · simp [startConfig, retag, FixedContentGammaAnchor.finalConfig, hg]
    · apply Fin.ext
      simp [startConfig, retag, FixedContentGammaAnchor.finalConfig, hg,
        FixedContentGammaTerminator.terminalIndex, Nat.min_eq_left (Nat.le_of_lt hlt)]
    · simp [startConfig, retag, FixedContentGammaAnchor.finalConfig, hg, marked]
  have hback : machine.run (zeros + 1) (startConfig B x w) =
      (⟨qBackSeen, ⟨7, by unfold tapeLength pairLength; omega⟩, marked⟩ :
        Config stateCount (pairLength a m) B) := by
    have hone : machine.run 1 (startConfig B x w) =
        (⟨qBackFirst, ⟨7 + zeros, by unfold tapeLength pairLength; omega⟩, marked⟩ :
          Config stateCount (pairLength a m) B) := by
      rw [UniformTM.run, hstart]
      simp only [UniformTM.run]
      rw [step_eq _ qBackFirst (some true) .left (by
        have hr := hmarked (8 + zeros) hlt (by omega)
        simpa [hr, show (Fin.append x w) ⟨8 + zeros, hlt⟩ = true by
          simpa [FixedContentTagGate.physicalSymbol, hlt] using ht] using start_true_action)]
      apply config_ext
      · rfl
      · apply Fin.ext; simp [moveHead, tapeLength, pairLength]
      · funext i; by_cases hi : i = ⟨8 + zeros, by unfold tapeLength pairLength; omega⟩ <;>
          simp [hi, hmarked (8 + zeros) hlt (by omega), htermBit]
    have hfirst : machine.run 1
        (⟨qBackFirst, ⟨7 + zeros, by unfold tapeLength pairLength; omega⟩, marked⟩ :
          Config stateCount (pairLength a m) B) =
        ⟨qBackSeen, ⟨6 + zeros, by unfold tapeLength pairLength; omega⟩, marked⟩ := by
      have hp := hz (zeros - 1) (by omega)
      have hpbit : (Fin.append x w) ⟨7 + zeros, by omega⟩ = false := by
        simpa [FixedContentTagGate.physicalSymbol,
          show 7 + zeros = 8 + (zeros - 1) by omega,
          show 8 + (zeros - 1) < a + m by omega] using hp
      simp only [UniformTM.run]
      rw [step_eq _ qBackSeen (some false) .left (by
        have hr := hmarked (7 + zeros) (by omega) (by omega)
        simpa [hr, hpbit] using backFirst_false_action)]
      apply config_ext <;> try rfl
      · apply Fin.ext; simp [moveHead]
      · funext i; by_cases hi : i = ⟨7 + zeros, by unfold tapeLength pairLength; omega⟩ <;>
          simp [hi, hmarked (7 + zeros) (by omega) (by omega), hpbit]
    have hloop (r : Nat) (hr : r ≤ zeros - 1) :
        machine.run r
          (⟨qBackSeen, ⟨6 + zeros, by unfold tapeLength pairLength; omega⟩, marked⟩ :
            Config stateCount (pairLength a m) B) =
          ⟨qBackSeen, ⟨6 + zeros - r, by unfold tapeLength pairLength; omega⟩, marked⟩ := by
      induction r with
      | zero => rfl
      | succ r ih =>
          have hp := hz (zeros - r - 2) (by omega)
          have hj : 6 + zeros - r = 8 + (zeros - r - 2) := by omega
          have hpbit : (Fin.append x w) ⟨6 + zeros - r, by omega⟩ = false := by
            simpa [FixedContentTagGate.physicalSymbol, hj,
              show 8 + (zeros - r - 2) < a + m by omega] using hp
          rw [UniformTM.run, ih (by omega), step_eq _ qBackSeen (some false) .left (by
            have hm := hmarked (6 + zeros - r) (by omega) (by omega)
            simpa [hm, hpbit] using backSeen_false_action)]
          apply config_ext
          · rfl
          · apply Fin.ext; simp [moveHead]; omega
          · funext i
            by_cases hi : i = ⟨6 + zeros - r, by unfold tapeLength pairLength; omega⟩ <;>
              simp [hi, hmarked (6 + zeros - r) (by omega) (by omega), hpbit]
    rw [show zeros + 1 = 1 + 1 + (zeros - 1) by omega, machine.run_add,
      machine.run_add, hone, hfirst, hloop (zeros - 1) (by omega)]
    congr 1
    apply Fin.ext
    simp
    omega
  have hhole : marked ⟨7, by unfold tapeLength pairLength; omega⟩ = none := by
    simp [marked, FixedContentGammaAnchor.markedTape]
  have hspend : machine.run 2
      (⟨qBackSeen, ⟨7, by unfold tapeLength pairLength; omega⟩, marked⟩ :
        Config stateCount (pairLength a m) B) =
      cursorConfig B x w qSeekTerm 9 (by unfold tapeLength pairLength; omega) := by
    have hA : machine.run 1
        (⟨qBackSeen, ⟨7, by unfold tapeLength pairLength; omega⟩, marked⟩ :
          Config stateCount (pairLength a m) B) =
        ⟨qSpend, ⟨8, by unfold tapeLength pairLength; omega⟩, marked⟩ := by
      simp only [UniformTM.run]
      rw [step_eq _ qSpend none .right (by simpa [hhole] using backSeen_none_action)]
      apply config_ext <;> try rfl
      · apply Fin.ext
        simp [moveHead, show 7 + 1 < tapeLength (pairLength a m) B by
          unfold tapeLength pairLength; omega]
      · funext i; by_cases hi : i.val = 7
        · have heq : i = ⟨7, by unfold tapeLength pairLength; omega⟩ := Fin.ext hi
          rw [heq]; simp [hhole]
        · simp [show i ≠ ⟨7, by unfold tapeLength pairLength; omega⟩ by
            intro h; exact hi (congrArg Fin.val h)]
    change machine.run 1 (machine.run 1
      (⟨qBackSeen, ⟨7, by unfold tapeLength pairLength; omega⟩, marked⟩ :
        Config stateCount (pairLength a m) B)) = _
    rw [hA]
    simp only [UniformTM.run]
    rw [step_eq _ qSeekTerm none .right (by
        have hm := hmarked 8 (by omega) (by omega)
        have hp := hz 0 hzero
        have hpbit : (Fin.append x w) ⟨8, by omega⟩ = false := by
          simpa [FixedContentTagGate.physicalSymbol, show 8 < a + m by omega] using hp
        simpa [hm, hpbit] using spend_false_action)]
    apply config_ext
    · rfl
    · apply Fin.ext
      simp [cursorConfig, moveHead, show 9 < tapeLength (pairLength a m) B by
        unfold tapeLength pairLength; omega]
    · funext i
      by_cases h7 : i.val = 7
      · have hi : i = ⟨7, by unfold tapeLength pairLength; omega⟩ := Fin.ext h7
        rw [hi]; simp [cursorConfig, openedTape, marked, FixedContentGammaAnchor.markedTape]
      · by_cases h8 : i.val = 8
        · have hi : i = ⟨8, by unfold tapeLength pairLength; omega⟩ := Fin.ext h8
          rw [hi]; simp [cursorConfig, openedTape]
        · have hne : i ≠ ⟨8, by unfold tapeLength pairLength; omega⟩ := by
            intro h; exact h8 (congrArg Fin.val h)
          simp [cursorConfig, openedTape, marked, FixedContentGammaAnchor.markedTape,
            h7, h8, hne]
  have hseek (r : Nat) (hr : r ≤ zeros - 1) :
      machine.run r (cursorConfig B x w qSeekTerm 9
        (by unfold tapeLength pairLength; omega)) =
      cursorConfig B x w qSeekTerm (9 + r)
        (by unfold tapeLength pairLength; omega) := by
    induction r with
    | zero => rfl
    | succ r ih =>
        rw [UniformTM.run, ih (by omega)]
        rw [step_cursor_keep x w qSeekTerm qSeekTerm _ .right (by
          have hp := hz (r + 1) (by omega)
          have hpbit : (Fin.append x w) ⟨9 + r, by omega⟩ = false := by
            have hp' := hp
            simp [FixedContentTagGate.physicalSymbol,
              show 8 + (r + 1) < a + m by omega] at hp'
            simpa [show 9 + r = 8 + (r + 1) by omega] using hp'
          have hc := content_at (B := B) x w (show 9 + r < a + m by omega)
          simpa [openedTape, show 9 + r ≠ 7 by omega, show 9 + r ≠ 8 by omega,
            hc, hpbit] using seek_false_action)]
        apply config_ext <;> try rfl
        apply Fin.ext
        simp [cursorConfig, moveHead, show 9 + r + 1 < tapeLength (pairLength a m) B by
          unfold tapeLength pairLength; omega]
        omega
  dsimp
  have htime : 2 * zeros + 3 = (zeros + 1) + 2 + (zeros - 1) + 1 := by omega
  have hseekEnd : machine.run (zeros - 1) (cursorConfig B x w qSeekTerm 9
      (by unfold tapeLength pairLength; omega)) =
      cursorConfig B x w qSeekTerm (8 + zeros)
        (by unfold tapeLength pairLength; omega) := by
    rw [hseek (zeros - 1) (by omega)]
    apply config_ext <;> try rfl
    apply Fin.ext
    simp [cursorConfig]
    omega
  rw [htime,
    machine.run_add, machine.run_add, machine.run_add, hback, hspend,
    hseekEnd, UniformTM.run]
  simp only [UniformTM.run]
  have hterm : openedTape B x w
      ⟨8 + zeros, by unfold tapeLength pairLength; omega⟩ = some true := by
    have hc := content_at (B := B) x w hlt
    simp [openedTape, show 8 + zeros ≠ 7 by omega, show zeros ≠ 0 by omega,
      hc, htermBit]
  rw [step_cursor_keep x w qSeekTerm qRead _ .right (by
    simpa [hterm] using seek_true_action)]
  refine ⟨rfl, ?_, rfl⟩
  simp [moveHead, show 8 + zeros + 1 < tapeLength (pairLength a m) B by
    unfold tapeLength pairLength; omega]
  omega

/-- The read-state partition is the executable heart of the first round. -/
theorem read_partition {N B : Nat} (c : Config stateCount N B) (hq : c.state = qRead) :
    ((c.tape c.head = some false →
        (machine.stepConfig c).state = qNextFalse ∧
        (machine.stepConfig c).head = c.head ∧
        (machine.stepConfig c).tape c.head = none) ∧
      (c.tape c.head = some true →
        (machine.stepConfig c).state = qRestoreOne ∧
        (machine.stepConfig c).head.val = c.head.val - 1 ∧
        (machine.stepConfig c).tape = c.tape) ∧
      (c.tape c.head = none →
        (machine.stepConfig c).state = qRestoreVirtual ∧
        (machine.stepConfig c).head.val = c.head.val - 1 ∧
        (machine.stepConfig c).tape = c.tape)) := by
  cases c with
  | mk state head tape =>
    change state = qRead at hq
    subst state
    dsimp at *
    constructor
    · intro h
      rw [step_eq _ qNextFalse none .stay (by simpa [h] using read_false_action)]
      simp [moveHead]
    constructor
    · intro h
      rw [step_eq _ qRestoreOne (some true) .left (by simpa [h] using read_true_action)]
      refine ⟨rfl, rfl, ?_⟩
      funext i
      by_cases hi : i = head <;> simp [hi, h]
    · intro h
      rw [step_eq _ qRestoreVirtual none .left (by simpa [h] using read_none_action)]
      refine ⟨rfl, rfl, ?_⟩
      funext i
      by_cases hi : i = head <;> simp [hi, h]

/-- The physical-false arm of the first round, including reachability from the
actual G2a handoff. -/
theorem first_physical_false_exact {a m B zeros : Nat}
    (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzero : 0 < zeros) (hp : 9 + zeros < a + m)
    (hfalse : (Fin.append x w) ⟨9 + zeros, hp⟩ = false) :
    NextInvariant B x w zeros
      (machine.run (2 * zeros + 4) (startConfig B x w)) := by
  have hr := first_read_reachable (B := B) x w htag hg hzero
  let hhead : 9 + zeros < tapeLength (pairLength a m) B := by
    unfold tapeLength pairLength; omega
  have hread : machine.run (2 * zeros + 3) (startConfig B x w) =
      cursorConfig B x w qRead (9 + zeros) hhead := by
    apply config_ext
    · exact hr.1
    · apply Fin.ext; exact hr.2.1
    · exact hr.2.2
  rw [show 2 * zeros + 4 = (2 * zeros + 3) + 1 by omega,
    machine.run_add, hread]
  simp only [UniformTM.run]
  rw [step_eq _ qNextFalse none .stay (by
      have hc := content_at (B := B) x w hp
      simpa [cursorConfig, openedTape, hp, hc, hfalse,
        show 9 + zeros ≠ 7 by omega, show 9 + zeros ≠ 8 by omega]
        using read_false_action)]
  refine ⟨rfl, by simp [cursorConfig, moveHead], ?_⟩
  funext i
  by_cases hi : i = ⟨9 + zeros, hhead⟩
  · subst i; simp [cursorConfig, nextTape]
  · have hiv : i.val ≠ 9 + zeros := by
      intro h; exact hi (Fin.ext h)
    simp [cursorConfig, nextTape, openedTape, hi, hiv]

/-- Zero width is a complete run: the first left step sees G2a's cell-7 hole,
restores literal `some false`, and stops without entering the payload. -/
theorem zero_width_exact {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some 0) :
    let c := machine.run 2 (startConfig B x w)
    c.state = qVirtual ∧ c.head.val = 7 ∧
      c.tape = FixedPairContentMarkerErase.contentTape B x w := by
  have hs := ((FixedContentGammaTerminator.gamma_contract _).1 0 hg).1
  have ht := ((FixedContentGammaTerminator.gamma_contract _).1 0 hg).2.1
  have hbit : (Fin.append x w) ⟨8, by omega⟩ = true := by
    simpa [FixedContentTagGate.physicalSymbol, hs] using ht
  have hbit7 : (Fin.append x w) ⟨7, by omega⟩ = false := by
    rcases FixedContentTagGate.tag_contract (Fin.append x w) with
      ⟨_, _, _, _, _, _, _, _, hc, hlen⟩
    have hL := hlen htag
    have hc := hc.mp htag
    simpa [FixedContentTagGate.expectedTagBit, FixedContentTagGate.physicalSymbol,
      show 7 < a + m by omega] using hc ⟨7, by decide⟩
  let base := FixedPairContentMarkerErase.contentTape B x w
  let marked := FixedContentGammaAnchor.markedTape B x w
  let h8 : 8 < tapeLength (pairLength a m) B := by unfold tapeLength pairLength; omega
  let h7 : 7 < tapeLength (pairLength a m) B := by unfold tapeLength pairLength; omega
  have hstart : startConfig B x w =
      (⟨qStart, ⟨8, h8⟩, marked⟩ : Config stateCount (pairLength a m) B) := by
    apply config_ext
    · simp [startConfig, retag, FixedContentGammaAnchor.finalConfig, hg]
    · apply Fin.ext
      simp [startConfig, retag, FixedContentGammaAnchor.finalConfig, hg,
        FixedContentGammaTerminator.terminalIndex, Nat.min_eq_left (Nat.le_of_lt hs)]
    · simp [startConfig, retag, FixedContentGammaAnchor.finalConfig, hg, marked]
  have hread8 : marked ⟨8, h8⟩ = some true := by
    simp [marked, FixedContentGammaAnchor.markedTape,
      FixedPairContentMarkerErase.contentTape, hs, hbit]
  have hone : machine.run 1 (startConfig B x w) =
      (⟨qBackFirst, ⟨7, h7⟩, marked⟩ : Config stateCount (pairLength a m) B) := by
    rw [UniformTM.run, hstart, step_eq _ qBackFirst (some true) .left (by
      simpa [UniformTM.run, hread8] using start_true_action)]
    apply config_ext
    · rfl
    · apply Fin.ext; simp [UniformTM.run, moveHead]
    · funext i
      by_cases hi : i = ⟨8, h8⟩ <;> simp [UniformTM.run, hi, hread8]
  have hread7 : marked ⟨7, h7⟩ = none := by
    simp [marked, FixedContentGammaAnchor.markedTape]
  dsimp
  rw [show 2 = 1 + 1 by omega, machine.run_add, hone, UniformTM.run,
    step_eq _ qVirtual (some false) .stay (by
      simpa [UniformTM.run, hread7] using backFirst_none_action)]
  refine ⟨rfl, by simp [UniformTM.run, moveHead], ?_⟩
  funext i
  by_cases hi : i.val = 7
  · have heq : i = ⟨7, h7⟩ := Fin.ext hi
    subst i
    simp [UniformTM.run, marked,
      FixedPairContentMarkerErase.contentTape, show 7 < a + m by omega, hbit7]
  · have hne : i ≠ ⟨7, h7⟩ := by intro h; exact hi (congrArg Fin.val h)
    simp [UniformTM.run, hne, marked, FixedContentGammaAnchor.markedTape, hi]

/-- At every branch exposed by this tracer the head is physical; its only
right moves have a strict successor cell, and its left moves are above zero.
These are the no-clamp arithmetic facts used by the trace proofs. -/
theorem tracer_no_clamp_facts {a m B zeros : Nat}
    (hgamma : 8 + zeros < a + m) :
    0 < 7 ∧ 8 < tapeLength (pairLength a m) B ∧
    8 + zeros + 1 < tapeLength (pairLength a m) B ∧
    9 + zeros ≤ a + m := by
  unfold tapeLength pairLength
  omega

/-- The complete write footprint of this core before a next-round handoff is
cell 7, cell 8, and (only on physical false) the first payload cell. -/
theorem nextTape_footprint {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (i : Fin (tapeLength (pairLength a m) B))
    (hi : i.val ≠ 7) (hi8 : i.val ≠ 8) (hip : i.val ≠ 9 + zeros) :
    nextTape B x w zeros i = FixedPairContentMarkerErase.contentTape B x w i := by
  simp [nextTape, hi, hi8, hip]

end Pnp3.Complexity.Uniform.V1.FixedGammaPayloadCursorCore
