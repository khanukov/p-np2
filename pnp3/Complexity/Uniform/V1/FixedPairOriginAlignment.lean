import Complexity.Uniform.V1.FixedPairOriginShiftBootstrap

namespace Pnp3.Complexity.Uniform.V1
namespace FixedPairOriginAlignment

open PairEncoding

abbrev alignmentStateCount : Nat := 26

def qStart : Fin alignmentStateCount := ⟨0, by decide⟩
def qAccept : Fin alignmentStateCount := ⟨24, by decide⟩
def qReject : Fin alignmentStateCount := ⟨25, by decide⟩

private def qNormalize : Fin alignmentStateCount := ⟨1, by decide⟩
private def qCheckAt : Fin alignmentStateCount := ⟨2, by decide⟩
private def qCheckSave : Fin alignmentStateCount := ⟨3, by decide⟩
private def qTryN : Fin alignmentStateCount := ⟨4, by decide⟩
private def qTryF : Fin alignmentStateCount := ⟨5, by decide⟩
private def qTryT : Fin alignmentStateCount := ⟨6, by decide⟩
private def qBounceN : Fin alignmentStateCount := ⟨7, by decide⟩
private def qBounceF : Fin alignmentStateCount := ⟨8, by decide⟩
private def qBounceT : Fin alignmentStateCount := ⟨9, by decide⟩
private def qClassN : Fin alignmentStateCount := ⟨10, by decide⟩
private def qClassF : Fin alignmentStateCount := ⟨11, by decide⟩
private def qClassT : Fin alignmentStateCount := ⟨12, by decide⟩
private def qRestoreN : Fin alignmentStateCount := ⟨13, by decide⟩
private def qRestoreF : Fin alignmentStateCount := ⟨14, by decide⟩
private def qRestoreT : Fin alignmentStateCount := ⟨15, by decide⟩
private def qCheckStepLeft : Fin alignmentStateCount := ⟨16, by decide⟩
private def qCheckNext : Fin alignmentStateCount := ⟨17, by decide⟩
private def qShiftTake : Fin alignmentStateCount := ⟨18, by decide⟩
private def qShiftPutF : Fin alignmentStateCount := ⟨19, by decide⟩
private def qShiftPutT : Fin alignmentStateCount := ⟨20, by decide⟩
private def qShiftGap : Fin alignmentStateCount := ⟨21, by decide⟩
private def qShiftInspect : Fin alignmentStateCount := ⟨22, by decide⟩
private def qShiftBack : Fin alignmentStateCount := ⟨23, by decide⟩

private def raw (q : Fin alignmentStateCount) (s : Option Bool) :
    Fin alignmentStateCount × Option Bool × Move :=
  match q.val with
  | 0 => match s with
    | none => (qNormalize, none, .left)
    | some b => (qReject, some b, .stay)
  | 1 => match s with
    | none => (qCheckAt, none, .left)
    | some b => (qCheckAt, some b, .right)
  | 2 => (qCheckSave, s, .right)
  | 3 => match s with
    | none => (qTryN, none, .left)
    | some false => (qTryF, none, .left)
    | some true => (qTryT, none, .left)
  | 4 => match s with
    | none => (qReject, none, .stay)
    | some b => (qBounceN, some b, .left)
  | 5 => match s with
    | none => (qReject, none, .stay)
    | some b => (qBounceF, some b, .left)
  | 6 => match s with
    | none => (qReject, none, .stay)
    | some b => (qBounceT, some b, .left)
  | 7 => (qClassN, s, .right)
  | 8 => (qClassF, s, .right)
  | 9 => (qClassT, s, .right)
  | 10 => match s with
    | none => (qAccept, none, .left)
    | some b => (qRestoreN, some b, .right)
  | 11 => match s with
    | none => (qAccept, some false, .left)
    | some b => (qRestoreF, some b, .right)
  | 12 => match s with
    | none => (qAccept, some true, .left)
    | some b => (qRestoreT, some b, .right)
  | 13 => match s with
    | none => (qCheckStepLeft, none, .left)
    | some b => (qReject, some b, .stay)
  | 14 => match s with
    | none => (qCheckStepLeft, some false, .left)
    | some b => (qReject, some b, .stay)
  | 15 => match s with
    | none => (qCheckStepLeft, some true, .left)
    | some b => (qReject, some b, .stay)
  | 16 => match s with
    | none => (qReject, none, .stay)
    | some b => (qCheckNext, some b, .left)
  | 17 => match s with
    | none => (qShiftTake, none, .right)
    | some b => (qCheckSave, some b, .right)
  | 18 => match s with
    | none => (qReject, none, .stay)
    | some false => (qShiftPutF, none, .left)
    | some true => (qShiftPutT, none, .left)
  | 19 => match s with
    | none => (qShiftGap, some false, .right)
    | some b => (qReject, some b, .stay)
  | 20 => match s with
    | none => (qShiftGap, some true, .right)
    | some b => (qReject, some b, .stay)
  | 21 => match s with
    | none => (qShiftInspect, none, .right)
    | some b => (qReject, some b, .stay)
  | 22 => match s with
    | none => (qShiftBack, none, .left)
    | some false => (qShiftPutF, none, .left)
    | some true => (qShiftPutT, none, .left)
  | 23 => match s with
    | none => (qCheckAt, none, .left)
    | some b => (qReject, some b, .stay)
  | 24 => (qAccept, s, .stay)
  | _ => (qReject, s, .stay)

def machine : UniformTM where
  stateCount := alignmentStateCount
  start := qStart
  accept := qAccept
  reject := qReject
  accept_ne_reject := by decide
  rawStep := raw

theorem raw_table (q : Fin alignmentStateCount) (s : Option Bool) :
    machine.rawStep q s = raw q s := rfl

theorem resource_pins :
    machine.stateCount = 26 ∧ machine.start = qStart ∧
    machine.accept = qAccept ∧ machine.reject = qReject ∧
    qStart.val = 0 ∧ qAccept.val = 24 ∧ qReject.val = 25 ∧
    Fintype.card (Fin machine.stateCount × Option Bool) = 78 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  change Fintype.card (Fin 26 × Option Bool) = 78
  decide

def retag {N B : Nat}
    (c : Config FixedPairOriginShiftBootstrap.shiftStateCount N B) :
    Config alignmentStateCount N B where
  state := qStart
  head := c.head
  tape := c.tape

def startConfig {n m : Nat} (B : Nat) (x : Bitstring n) (w : Bitstring m) :
    Config alignmentStateCount (pairLength n m) B :=
  retag (FixedPairOriginShiftBootstrap.finalConfig B x w)

def clock (n m : Nat) : Nat := (10 * n + 7) * (n + m + 1) + 3 * n

private def K (n m : Nat) : Nat := n + m + 1

private def bit {n m : Nat} (x : Bitstring n) (w : Bitstring m) (r : Nat) : Bool :=
  if h : r < n + m then Fin.append x w ⟨r, h⟩ else true

private def blockCell {n m : Nat} (x : Bitstring n) (w : Bitstring m)
    (p k : Nat) : Option Bool :=
  if p ≤ k ∧ k < p + K n m then some (bit x w (k - p)) else none

private def blockTape {n m : Nat} (B : Nat) (x : Bitstring n)
    (w : Bitstring m) (p : Nat) :
    Fin (tapeLength (pairLength n m) B) → Option Bool :=
  fun i => blockCell x w p i.val

def alignedTape {n m : Nat} (B : Nat) (x : Bitstring n) (w : Bitstring m) :
    Fin (tapeLength (pairLength n m) B) → Option Bool :=
  blockTape B x w 0

def finalConfig {n m : Nat} (B : Nat) (x : Bitstring n) (w : Bitstring m) :
    Config alignmentStateCount (pairLength n m) B where
  state := qAccept
  head := ⟨0, by unfold tapeLength; omega⟩
  tape := alignedTape B x w

theorem handoff_exact {n m B : Nat} (x : Bitstring n) (w : Bitstring m) :
    let p := FixedPairOriginShiftBootstrap.machine.run
      (FixedPairOriginShiftBootstrap.clock n m)
      (FixedPairOriginShiftBootstrap.startConfig B x w)
    p = FixedPairOriginShiftBootstrap.finalConfig B x w ∧
    p.state = FixedPairOriginShiftBootstrap.qAccept ∧
    (startConfig B x w).state = qStart ∧
    (startConfig B x w).head = p.head ∧
    (startConfig B x w).tape = p.tape := by
  dsimp
  rw [FixedPairOriginShiftBootstrap.run_exact]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem clock_exact (n m : Nat) :
    clock n m = 2 + n * (10 * (n + m + 1) + 3) +
        (7 * ((n + m + 1) - 1) + 5) ∧
    clock n m = 10 * n * n + 10 * n * m + 20 * n + 7 * m + 7 ∧
    clock 0 0 = 7 ∧
    clock n m ≤ (10 * (n + m + 1) + 7) * (n + m + 1) +
      3 * (n + m + 1) := by
  unfold clock
  refine ⟨?_, by ring, rfl, ?_⟩
  · rw [show n + m + 1 - 1 = n + m by omega]
    ring
  exact Nat.add_le_add
    (Nat.mul_le_mul_right _ (Nat.add_le_add_right
      (Nat.mul_le_mul_left 10 (show n ≤ n + m + 1 by omega)) 7))
    (Nat.mul_le_mul_left 3 (show n ≤ n + m + 1 by omega))
private theorem pair_eq (n m : Nat) : pairLength n m = n + K n m := by
  unfold pairLength K
  omega
private theorem bit_append {n m : Nat} (x : Bitstring n) (w : Bitstring m)
    (j : Fin (n + m)) : bit x w j.val = Fin.append x w j := by
  simp [bit, j.isLt]
private theorem bit_x {n m : Nat} (x : Bitstring n) (w : Bitstring m)
    (j : Fin n) : bit x w j.val = x j := by
  exact (bit_append x w (Fin.castAdd m j)).trans (Fin.append_left x w j)
private theorem bit_w {n m : Nat} (x : Bitstring n) (w : Bitstring m)
    (j : Fin m) : bit x w (n + j.val) = w j := by
  exact (bit_append x w (Fin.natAdd n j)).trans (Fin.append_right x w j)
private theorem bit_marker {n m : Nat} (x : Bitstring n) (w : Bitstring m) :
    bit x w (n + m) = true := by simp [bit]
private theorem bootstrap_tape {n m B : Nat} (x : Bitstring n)
    (w : Bitstring m) :
    (startConfig B x w).tape = blockTape B x w n := by
  have h := FixedPairOriginShiftBootstrap.final_layout (B := B) x w
  rw [FixedPairOriginShiftBootstrap.run_exact] at h
  dsimp at h
  funext i
  change FixedPairOriginShiftBootstrap.shiftedTape B x w i = blockCell x w n i.val
  have hp := pair_eq n m
  by_cases hi : n ≤ i.val ∧ i.val < pairLength n m
  · unfold blockCell
    rw [if_pos (by omega)]
    by_cases hx : i.val < 2 * n
    · let j : Fin n := ⟨i.val - n, by omega⟩
      have hij : i = ⟨n + j.val, by unfold tapeLength pairLength; omega⟩ :=
        Fin.ext (by dsimp [j]; omega)
      have hv := h.2.1 j
      change FixedPairOriginShiftBootstrap.shiftedTape B x w _ = some (x j) at hv
      rw [hij, hv, show n + j.val - n = j.val by omega, bit_x]
    · by_cases hw : i.val < 2 * n + m
      · let j : Fin m := ⟨i.val - 2 * n, by omega⟩
        have hij : i = ⟨2 * n + j.val, by unfold tapeLength pairLength; omega⟩ :=
          Fin.ext (by dsimp [j]; omega)
        have hv := h.2.2.1 j
        change FixedPairOriginShiftBootstrap.shiftedTape B x w _ = some (w j) at hv
        rw [hij, hv, show 2 * n + j.val - n = n + j.val by omega,
          bit_w]
      · have hie : i.val = 2 * n + m := by unfold pairLength at hi; omega
        have hij : i = ⟨2 * n + m, by unfold tapeLength pairLength; omega⟩ :=
          Fin.ext hie
        have hv := h.2.2.2.1
        change FixedPairOriginShiftBootstrap.shiftedTape B x w _ = some true at hv
        rw [hij, hv, show 2 * n + m - n = n + m by omega,
          bit_marker]
  · unfold blockCell
    rw [if_neg (by omega)]
    by_cases hl : i.val < n
    · exact h.1 i hl
    · exact h.2.2.2.2 i (by omega)
private theorem block_read {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {p k : Nat} (hl : p ≤ k) (hr : k < p + K n m)
    (h : Fin (tapeLength (pairLength n m) B)) (hh : h.val = k) :
    blockTape B x w p h = some (bit x w (k - p)) := by
  change blockCell x w p h.val = _
  unfold blockCell
  rw [if_pos (by omega), show h.val - p = k - p by omega]
private theorem block_blank {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {p k : Nat} (hblank : k < p ∨ p + K n m ≤ k)
    (h : Fin (tapeLength (pairLength n m) B)) (hh : h.val = k) :
    blockTape B x w p h = none := by
  change blockCell x w p h.val = none
  unfold blockCell
  rw [if_neg (by omega)]
private theorem block_zero {n m B : Nat} (x : Bitstring n) (w : Bitstring m) :
    blockTape B x w 0 = alignedTape B x w := rfl
private def cell {n m : Nat} (B k : Nat) (hk : k ≤ pairLength n m) :
    Fin (tapeLength (pairLength n m) B) :=
  ⟨k, by unfold tapeLength; omega⟩
private theorem cell_val {n m B k : Nat} (hk : k ≤ pairLength n m) :
    (cell (n := n) (m := m) B k hk).val = k := rfl
private theorem config_ext {N B : Nat}
    {c d : Config alignmentStateCount N B} (hs : c.state = d.state)
    (hh : c.head = d.head) (ht : c.tape = d.tape) : c = d := by
  cases c
  cases d
  cases hs
  cases hh
  cases ht
  rfl
private theorem stepConfig_eq {N B : Nat}
    (c : Config alignmentStateCount N B) (q : Fin alignmentStateCount)
    (s : Option Bool) (mv : Move)
    (ha : machine.step c.state (c.tape c.head) = (q, s, mv)) :
    machine.stepConfig c =
      ({ state := q, head := moveHead c.head mv,
         tape := fun i => if i = c.head then s else c.tape i } :
        Config alignmentStateCount N B) := by
  apply config_ext
  · change (machine.step c.state (c.tape c.head)).1 = q
    rw [ha]
  · change moveHead c.head (machine.step c.state (c.tape c.head)).2.2 = _
    rw [ha]
  · funext i
    change (if i = c.head then (machine.step c.state (c.tape c.head)).2.1
      else c.tape i) = (if i = c.head then s else c.tape i)
    rw [ha]
private theorem move_right_val {L : Nat} (h : Fin L) (hb : h.val + 1 < L) :
    (moveHead h .right).val = h.val + 1 := by
  unfold moveHead
  rw [dif_pos hb]
private def checkState (j : Nat) : Fin alignmentStateCount :=
  if j = 0 then qCheckAt else qCheckNext
private def savedState (r : Option Bool) : Fin alignmentStateCount :=
  match r with | none => qTryN | some false => qTryF | some true => qTryT
private def bounceState (r : Option Bool) : Fin alignmentStateCount :=
  match r with | none => qBounceN | some false => qBounceF | some true => qBounceT
private def classState (r : Option Bool) : Fin alignmentStateCount :=
  match r with | none => qClassN | some false => qClassF | some true => qClassT
private def restoreState (r : Option Bool) : Fin alignmentStateCount :=
  match r with | none => qRestoreN | some false => qRestoreF | some true => qRestoreT
private def putState (b : Bool) : Fin alignmentStateCount :=
  if b then qShiftPutT else qShiftPutF
private def clearCell {n m : Nat} (x : Bitstring n) (w : Bitstring m)
    (p j k : Nat) : Option Bool :=
  if k = p + K n m - j then none else blockCell x w p k
private def clearTape {n m : Nat} (B : Nat) (x : Bitstring n)
    (w : Bitstring m) (p j : Nat) :
    Fin (tapeLength (pairLength n m) B) → Option Bool :=
  fun i => clearCell x w p j i.val
private def checkConfig {n m : Nat} (B : Nat) (x : Bitstring n)
    (w : Bitstring m) (p j : Nat) (hp : p ≤ n) (hj : j ≤ K n m) :
    Config alignmentStateCount (pairLength n m) B where
  state := checkState j
  head := cell B (p + K n m - 1 - j) (by rw [pair_eq]; omega)
  tape := blockTape B x w p
private def saveConfig {n m : Nat} (B : Nat) (x : Bitstring n)
    (w : Bitstring m) (p j : Nat) (hp : p ≤ n) (hj : j < K n m) :
    Config alignmentStateCount (pairLength n m) B where
  state := qCheckSave
  head := cell B (p + K n m - j) (by rw [pair_eq]; omega)
  tape := blockTape B x w p
private def tryConfig {n m : Nat} (B : Nat) (x : Bitstring n)
    (w : Bitstring m) (p j : Nat) (hp : p ≤ n) (hj : j < K n m) :
    Config alignmentStateCount (pairLength n m) B where
  state := savedState (blockCell x w p (p + K n m - j))
  head := cell B (p + K n m - 1 - j) (by rw [pair_eq]; omega)
  tape := clearTape B x w p j
private def bounceConfig {n m : Nat} (B : Nat) (x : Bitstring n)
    (w : Bitstring m) (p j : Nat) (hp : p ≤ n) (hj : j < K n m) :
    Config alignmentStateCount (pairLength n m) B where
  state := bounceState (blockCell x w p (p + K n m - j))
  head := cell B (p + K n m - 1 - j - 1) (by rw [pair_eq]; omega)
  tape := clearTape B x w p j
private def classConfig {n m : Nat} (B : Nat) (x : Bitstring n)
    (w : Bitstring m) (p j : Nat) (hp : p ≤ n) (hj : j < K n m) :
    Config alignmentStateCount (pairLength n m) B where
  state := classState (blockCell x w p (p + K n m - j))
  head := cell B (p + K n m - 1 - j) (by rw [pair_eq]; omega)
  tape := clearTape B x w p j
private def restoreConfig {n m : Nat} (B : Nat) (x : Bitstring n)
    (w : Bitstring m) (p j : Nat) (hp : p ≤ n) (hj : j < K n m) :
    Config alignmentStateCount (pairLength n m) B where
  state := restoreState (blockCell x w p (p + K n m - j))
  head := cell B (p + K n m - j) (by rw [pair_eq]; omega)
  tape := clearTape B x w p j
private def leftConfig {n m : Nat} (B : Nat) (x : Bitstring n)
    (w : Bitstring m) (p j : Nat) (hp : p ≤ n) (hj : j < K n m) :
    Config alignmentStateCount (pairLength n m) B where
  state := qCheckStepLeft
  head := cell B (p + K n m - 1 - j) (by rw [pair_eq]; omega)
  tape := blockTape B x w p
private theorem save_action (r : Option Bool) :
    machine.step qCheckSave r = (savedState r, none, .left) := by
  cases r with
  | none => rfl
  | some b => cases b <;> rfl

private theorem try_action (r : Option Bool) (b : Bool) :
    machine.step (savedState r) (some b) = (bounceState r, some b, .left) := by
  cases r with
  | none => cases b <;> rfl
  | some a => cases a <;> cases b <;> rfl

private theorem bounce_action (r a : Option Bool) :
    machine.step (bounceState r) a = (classState r, a, .right) := by
  cases r with
  | none => rfl
  | some b => cases b <;> rfl

private theorem class_some (r : Option Bool) (b : Bool) :
    machine.step (classState r) (some b) =
      (restoreState r, some b, .right) := by
  cases r with
  | none => cases b <;> rfl
  | some a => cases a <;> cases b <;> rfl

private theorem class_none (r : Option Bool) :
    machine.step (classState r) none = (qAccept, r, .left) := by
  cases r with
  | none => rfl
  | some b => cases b <;> rfl

private theorem restore_action (r : Option Bool) :
    machine.step (restoreState r) none = (qCheckStepLeft, r, .left) := by
  cases r with
  | none => rfl
  | some b => cases b <;> rfl

private theorem checkAt_action (a : Option Bool) :
    machine.step qCheckAt a = (qCheckSave, a, .right) := rfl

private theorem checkNext_some (b : Bool) :
    machine.step qCheckNext (some b) = (qCheckSave, some b, .right) := by
  cases b <;> rfl

private theorem left_some (b : Bool) :
    machine.step qCheckStepLeft (some b) = (qCheckNext, some b, .left) := by
  cases b <;> rfl

private theorem check_read {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {p j : Nat} (hp : p ≤ n) (hj : j < K n m) :
    (checkConfig B x w p j hp (by omega)).tape
      (checkConfig B x w p j hp (by omega)).head =
        some (bit x w (K n m - 1 - j)) := by
  change blockCell x w p (p + K n m - 1 - j) = _
  unfold blockCell
  rw [if_pos (by omega), show p + K n m - 1 - j - p = K n m - 1 - j by omega]

private theorem save_read {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {p j : Nat} (hp : p ≤ n) (hj : j < K n m) :
    (saveConfig B x w p j hp hj).tape (saveConfig B x w p j hp hj).head =
      blockCell x w p (p + K n m - j) := rfl

private theorem try_read {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {p j : Nat} (hp : p ≤ n) (hj : j < K n m) :
    (tryConfig B x w p j hp hj).tape (tryConfig B x w p j hp hj).head =
      some (bit x w (K n m - 1 - j)) := by
  change clearCell x w p j (p + K n m - 1 - j) = _
  unfold clearCell
  rw [if_neg (by omega)]
  unfold blockCell
  rw [if_pos (by omega), show p + K n m - 1 - j - p = K n m - 1 - j by omega]

private theorem class_read {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {p j : Nat} (hp : p ≤ n) (hj : j < K n m) :
    (classConfig B x w p j hp hj).tape
      (classConfig B x w p j hp hj).head =
        some (bit x w (K n m - 1 - j)) := by
  change clearCell x w p j (p + K n m - 1 - j) = _
  unfold clearCell
  rw [if_neg (by omega)]
  unfold blockCell
  rw [if_pos (by omega), show p + K n m - 1 - j - p = K n m - 1 - j by omega]

private theorem restore_read {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {p j : Nat} (hp : p ≤ n) (hj : j < K n m) :
    (restoreConfig B x w p j hp hj).tape
      (restoreConfig B x w p j hp hj).head = none := by
  change clearCell x w p j (p + K n m - j) = none
  unfold clearCell
  rw [if_pos rfl]

private theorem erase_neighbor {n m B : Nat} (x : Bitstring n)
    (w : Bitstring m) {p j : Nat} (hp : p ≤ n) (hj : j < K n m) :
    (fun i => if i = (saveConfig B x w p j hp hj).head then none
      else (saveConfig B x w p j hp hj).tape i) = clearTape B x w p j := by
  funext i
  unfold saveConfig clearTape clearCell
  by_cases hi : i.val = p + K n m - j
  · have he : i = cell B (p + K n m - j) (by rw [pair_eq]; omega) := Fin.ext hi
    rw [if_pos he, if_pos hi]
  · have he : i ≠ cell B (p + K n m - j) (by rw [pair_eq]; omega) :=
      fun h => hi (congrArg Fin.val h)
    rw [if_neg he, if_neg hi]
    rfl

private theorem restore_neighbor {n m B : Nat} (x : Bitstring n)
    (w : Bitstring m) {p j : Nat} (hp : p ≤ n) (hj : j < K n m) :
    (fun i => if i = (restoreConfig B x w p j hp hj).head then
        blockCell x w p (p + K n m - j)
      else (restoreConfig B x w p j hp hj).tape i) = blockTape B x w p := by
  funext i
  change (if i = cell B (p + K n m - j) (by rw [pair_eq]; omega) then
      blockCell x w p (p + K n m - j)
    else clearCell x w p j i.val) = blockCell x w p i.val
  unfold clearCell
  by_cases hi : i.val = p + K n m - j
  · have he : i = cell B (p + K n m - j) (by rw [pair_eq]; omega) := Fin.ext hi
    rw [if_pos he]
    exact congrArg (blockCell x w p) hi.symm
  · have he : i ≠ cell B (p + K n m - j) (by rw [pair_eq]; omega) :=
      fun h => hi (congrArg Fin.val h)
    rw [if_neg he, if_neg hi]

private theorem step_check {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {p j : Nat} (hp : p ≤ n) (hj : j < K n m) :
    machine.stepConfig (checkConfig B x w p j hp (by omega)) =
      saveConfig B x w p j hp hj := by
  have hr := check_read (B := B) x w hp hj
  have ha : machine.step (checkConfig B x w p j hp (by omega)).state
      ((checkConfig B x w p j hp (by omega)).tape
        (checkConfig B x w p j hp (by omega)).head) =
      (qCheckSave, some (bit x w (K n m - 1 - j)), .right) := by
    rw [hr]
    change machine.step (checkState j) (some (bit x w (K n m - 1 - j))) = _
    by_cases h0 : j = 0
    · rw [show checkState j = qCheckAt by simp [checkState, h0]]
      exact checkAt_action _
    · rw [show checkState j = qCheckNext by simp [checkState, h0]]
      exact checkNext_some _
  rw [stepConfig_eq _ _ _ _ ha]
  apply config_ext
  · rfl
  · apply Fin.ext
    rw [move_right_val _ (by
      change p + K n m - 1 - j + 1 < tapeLength (pairLength n m) B
      unfold tapeLength
      rw [pair_eq]
      omega)]
    change p + K n m - 1 - j + 1 = p + K n m - j
    omega
  · change (fun i => if i = (checkConfig B x w p j hp _).head then
        some (bit x w (K n m - 1 - j)) else blockTape B x w p i) =
      blockTape B x w p
    funext i
    by_cases hi : i = (checkConfig B x w p j hp (by omega)).head
    · rw [if_pos hi]
      subst i
      exact hr.symm
    · rw [if_neg hi]

private theorem step_save {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {p j : Nat} (hp : p ≤ n) (hj : j < K n m) :
    machine.stepConfig (saveConfig B x w p j hp hj) =
      tryConfig B x w p j hp hj := by
  rw [stepConfig_eq _ _ _ _ (by rw [save_read x w hp hj]; exact save_action _)]
  apply config_ext
  · rfl
  · apply Fin.ext
    change p + K n m - j - 1 = p + K n m - 1 - j
    omega
  · exact erase_neighbor x w hp hj

private theorem step_try {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {p j : Nat} (hp : p ≤ n) (hj : j < K n m) :
    machine.stepConfig (tryConfig B x w p j hp hj) =
      bounceConfig B x w p j hp hj := by
  rw [stepConfig_eq _ _ _ _ (by rw [try_read x w hp hj]; exact try_action _ _)]
  apply config_ext
  · rfl
  · apply Fin.ext
    change p + K n m - 1 - j - 1 = _
    rfl
  · change (fun i => if i = (tryConfig B x w p j hp hj).head then
        some (bit x w (K n m - 1 - j)) else clearTape B x w p j i) =
      clearTape B x w p j
    funext i
    by_cases hi : i = (tryConfig B x w p j hp hj).head
    · rw [if_pos hi]
      subst i
      exact (try_read (B := B) x w hp hj).symm
    · rw [if_neg hi]

private theorem step_bounce {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {p j : Nat} (hp : p ≤ n) (hj : j < K n m)
    (hpos : 0 < p + K n m - 1 - j) :
    machine.stepConfig (bounceConfig B x w p j hp hj) =
      classConfig B x w p j hp hj := by
  rw [stepConfig_eq _ _ _ _ (bounce_action _ _)]
  apply config_ext
  · rfl
  · apply Fin.ext
    rw [move_right_val _ (by
      change (p + K n m - 1 - j - 1) + 1 < tapeLength (pairLength n m) B
      unfold tapeLength
      rw [pair_eq]
      omega)]
    change (p + K n m - 1 - j - 1) + 1 = p + K n m - 1 - j
    omega
  · change (fun i => if i = (bounceConfig B x w p j hp hj).head then
        clearTape B x w p j (bounceConfig B x w p j hp hj).head
      else clearTape B x w p j i) = clearTape B x w p j
    funext i
    by_cases hi : i = (bounceConfig B x w p j hp hj).head
    · rw [if_pos hi]
      exact congrArg (clearTape B x w p j) hi.symm
    · rw [if_neg hi]

private theorem step_class {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {p j : Nat} (hp : p ≤ n) (hj : j < K n m)
    (hpos : 0 < p + K n m - 1 - j) :
    machine.stepConfig (classConfig B x w p j hp hj) =
      restoreConfig B x w p j hp hj := by
  rw [stepConfig_eq _ _ _ _ (by rw [class_read x w hp hj]; exact class_some _ _)]
  apply config_ext
  · rfl
  · apply Fin.ext
    rw [move_right_val _ (by
      change p + K n m - 1 - j + 1 < tapeLength (pairLength n m) B
      unfold tapeLength
      rw [pair_eq]
      omega)]
    change p + K n m - 1 - j + 1 = p + K n m - j
    omega
  · change (fun i => if i = (classConfig B x w p j hp hj).head then
        some (bit x w (K n m - 1 - j)) else clearTape B x w p j i) =
      clearTape B x w p j
    funext i
    by_cases hi : i = (classConfig B x w p j hp hj).head
    · rw [if_pos hi]
      subst i
      exact (class_read (B := B) x w hp hj).symm
    · rw [if_neg hi]

private theorem step_restore {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {p j : Nat} (hp : p ≤ n) (hj : j < K n m) :
    machine.stepConfig (restoreConfig B x w p j hp hj) =
      leftConfig B x w p j hp hj := by
  rw [stepConfig_eq _ _ _ _ (by rw [restore_read x w hp hj]; exact restore_action _)]
  apply config_ext
  · rfl
  · apply Fin.ext
    change p + K n m - j - 1 = p + K n m - 1 - j
    omega
  · exact restore_neighbor x w hp hj

private theorem step_left {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {p j : Nat} (hp : p ≤ n) (hj : j < K n m)
    (hpos : 0 < p + K n m - 1 - j) :
    machine.stepConfig (leftConfig B x w p j hp hj) =
      checkConfig B x w p (j + 1) hp (by omega) := by
  have hr0 := block_read x w (B := B) (p := p) (k := p + K n m - 1 - j)
    (by omega) (by omega) (leftConfig B x w p j hp hj).head rfl
  have hr : (leftConfig B x w p j hp hj).tape
      (leftConfig B x w p j hp hj).head =
        some (bit x w (K n m - 1 - j)) := by
    simpa only [show p + K n m - 1 - j - p = K n m - 1 - j by omega] using hr0
  rw [stepConfig_eq _ _ _ _ (by rw [hr]; exact left_some _)]
  apply config_ext
  · change qCheckNext = checkState (j + 1)
    unfold checkState
    rw [if_neg (by omega)]
  · apply Fin.ext
    change p + K n m - 1 - j - 1 = p + K n m - 1 - (j + 1)
    omega
  · change (fun i => if i = (leftConfig B x w p j hp hj).head then
        some (bit x w (K n m - 1 - j)) else blockTape B x w p i) =
      blockTape B x w p
    funext i
    by_cases hi : i = (leftConfig B x w p j hp hj).head
    · rw [if_pos hi]
      subst i
      exact hr.symm
    · rw [if_neg hi]

private theorem check_nonorigin {n m B : Nat} (x : Bitstring n)
    (w : Bitstring m) {p j : Nat} (hp : p ≤ n) (hj : j < K n m)
    (hpos : 0 < p + K n m - 1 - j) :
    machine.run 7 (checkConfig B x w p j hp (by omega)) =
      checkConfig B x w p (j + 1) hp (by omega) := by
  change machine.stepConfig (machine.stepConfig (machine.stepConfig
    (machine.stepConfig (machine.stepConfig (machine.stepConfig
      (machine.stepConfig (checkConfig B x w p j hp (by omega)))))))) = _
  rw [step_check x w hp hj, step_save x w hp hj, step_try x w hp hj,
    step_bounce x w hp hj hpos, step_class x w hp hj hpos,
    step_restore x w hp hj, step_left x w hp hj hpos]

private def originClassConfig {n m : Nat} (B : Nat) (x : Bitstring n)
    (w : Bitstring m) : Config alignmentStateCount (pairLength n m) B where
  state := classState (blockCell x w 0 1)
  head := cell B 1 (by unfold pairLength; omega)
  tape := clearTape B x w 0 (K n m - 1)

private theorem step_bounce_origin {n m B : Nat} (x : Bitstring n)
    (w : Bitstring m) :
    machine.stepConfig (bounceConfig B x w 0 (K n m - 1)
      (by omega) (by unfold K; omega)) =
      originClassConfig B x w := by
  rw [stepConfig_eq _ _ _ _ (bounce_action _ _)]
  apply config_ext
  · change classState (blockCell x w 0 (0 + K n m - (K n m - 1))) =
      classState (blockCell x w 0 1)
    congr 2
    unfold K
    omega
  · apply Fin.ext
    rw [move_right_val _ (by
      change (0 + K n m - 1 - (K n m - 1) - 1) + 1 <
        tapeLength (pairLength n m) B
      unfold tapeLength pairLength K
      omega)]
    change (0 + K n m - 1 - (K n m - 1) - 1) + 1 = 1
    unfold K
    omega
  · change (fun i => if i = _ then
      clearTape B x w 0 (K n m - 1) _
      else clearTape B x w 0 (K n m - 1) i) = _
    funext i
    by_cases hi : i = (bounceConfig B x w 0 (K n m - 1)
        (by omega) (by unfold K; omega)).head
    · rw [if_pos hi]
      exact congrArg _ hi.symm
    · rw [if_neg hi]
      rfl

private theorem origin_read {n m B : Nat} (x : Bitstring n) (w : Bitstring m) :
    (originClassConfig B x w).tape (originClassConfig B x w).head = none := by
  change clearCell x w 0 (K n m - 1) 1 = none
  unfold clearCell
  rw [if_pos (by unfold K; omega)]

private theorem restore_origin {n m B : Nat} (x : Bitstring n) (w : Bitstring m) :
    (fun i => if i = (originClassConfig B x w).head then blockCell x w 0 1
      else (originClassConfig B x w).tape i) = alignedTape B x w := by
  funext i
  change (if i = cell B 1 (by unfold pairLength; omega) then blockCell x w 0 1
    else clearCell x w 0 (K n m - 1) i.val) = blockCell x w 0 i.val
  unfold clearCell
  by_cases hi : i.val = 1
  · have he : i = cell B 1 (by unfold pairLength; omega) := Fin.ext hi
    rw [if_pos he]
    exact congrArg (blockCell x w 0) hi.symm
  · have he : i ≠ cell B 1 (by unfold pairLength; omega) :=
      fun h => hi (congrArg Fin.val h)
    rw [if_neg he, if_neg (by unfold K; omega)]

private theorem step_origin {n m B : Nat} (x : Bitstring n) (w : Bitstring m) :
    machine.stepConfig (originClassConfig B x w) = finalConfig B x w := by
  rw [stepConfig_eq _ _ _ _ (by rw [origin_read x w]; exact class_none _)]
  apply config_ext
  · rfl
  · apply Fin.ext
    rfl
  · exact restore_origin x w

private theorem check_origin {n m B : Nat} (x : Bitstring n) (w : Bitstring m) :
    machine.run 5 (checkConfig B x w 0 (K n m - 1)
      (by omega) (by unfold K; omega)) =
      finalConfig B x w := by
  simp only [UniformTM.run]
  rw [step_check x w (by omega) (by unfold K; omega),
    step_save x w (by omega) (by unfold K; omega),
    step_try x w (by omega) (by unfold K; omega), step_bounce_origin x w,
    step_origin x w]

private theorem scan_prefix {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {p : Nat} (hp : p ≤ n) (j : Nat) (hj : j ≤ K n m)
    (hstop : 0 < p ∨ j ≤ K n m - 1) :
    machine.run (7 * j) (checkConfig B x w p 0 hp (by omega)) =
      checkConfig B x w p j hp hj := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [show 7 * (j + 1) = 7 * j + 7 by ring, machine.run_add,
        ih (by omega) (by omega), check_nonorigin x w hp (by omega) (by omega)]

private theorem final_scan {n m B : Nat} (x : Bitstring n) (w : Bitstring m) :
    machine.run (7 * (K n m - 1) + 5)
      (checkConfig B x w 0 0 (by omega) (by omega)) = finalConfig B x w := by
  rw [machine.run_add, scan_prefix x w (p := 0) (by omega)
      (K n m - 1) (by omega) (Or.inr (le_refl _)), check_origin x w]

private def rollCell {n m : Nat} (x : Bitstring n) (w : Bitstring m)
    (p r k : Nat) : Option Bool :=
  if k < p - 1 then none
  else if k < p - 1 + r then some (bit x w (k - (p - 1)))
  else if k < p + r then none
  else if k < p + K n m then some (bit x w (k - p))
  else none

private def rollTape {n m : Nat} (B : Nat) (x : Bitstring n)
    (w : Bitstring m) (p r : Nat) :
    Fin (tapeLength (pairLength n m) B) → Option Bool :=
  fun i => rollCell x w p r i.val

private def takenTape {n m : Nat} (B : Nat) (x : Bitstring n)
    (w : Bitstring m) (p r : Nat) :
    Fin (tapeLength (pairLength n m) B) → Option Bool :=
  fun i => if i.val = p + r then none else rollCell x w p r i.val

private theorem roll_zero {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {p : Nat} (hpos : 0 < p) : rollTape B x w p 0 = blockTape B x w p := by
  funext i
  change rollCell x w p 0 i.val = blockCell x w p i.val
  unfold rollCell blockCell
  simp only [Nat.add_zero]
  by_cases hll : i.val < p - 1
  · rw [if_pos hll, if_neg (by omega)]
  · rw [if_neg hll, if_neg (by omega)]
    by_cases hl : i.val < p
    · rw [if_pos hl, if_neg (by omega)]
    · rw [if_neg hl]
      by_cases hr : i.val < p + K n m
      · rw [if_pos hr, if_pos ⟨by omega, hr⟩]
      · rw [if_neg hr, if_neg (by omega)]

private theorem roll_last {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {p : Nat} :
    rollTape B x w p (K n m) = blockTape B x w (p - 1) := by
  funext i
  change rollCell x w p (K n m) i.val = blockCell x w (p - 1) i.val
  unfold rollCell blockCell
  by_cases hl : i.val < p - 1
  · rw [if_pos hl, if_neg (by omega)]
  · by_cases hr : i.val < p - 1 + K n m
    · rw [if_neg hl, if_pos hr, if_pos (by omega)]
    · rw [if_neg hl, if_neg hr]
      by_cases he : i.val < p + K n m
      · rw [if_pos he, if_neg (by omega)]
      · rw [if_neg he, if_neg (by omega), if_neg (by omega)]

private theorem erase_source {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {p r : Nat} (hp : p ≤ n) (hr : r < K n m) :
    (fun i => if i = cell B (p + r) (by rw [pair_eq]; omega) then none
      else rollTape B x w p r i) = takenTape B x w p r := by
  funext i
  change (if i = cell B (p + r) (by rw [pair_eq]; omega) then none
    else rollCell x w p r i.val) =
      if i.val = p + r then none else rollCell x w p r i.val
  by_cases hi : i.val = p + r
  · have he : i = cell B (p + r) (by rw [pair_eq]; omega) := Fin.ext hi
    rw [if_pos he, if_pos hi]
  · have he : i ≠ cell B (p + r) (by rw [pair_eq]; omega) :=
      fun h => hi (congrArg Fin.val h)
    rw [if_neg he, if_neg hi]

private theorem fill_hole {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {p r : Nat} (hp : p ≤ n) (hpos : 0 < p) (hr : r < K n m) :
    (fun i => if i = cell B (p + r - 1) (by rw [pair_eq]; omega) then
        some (bit x w r) else takenTape B x w p r i) =
      rollTape B x w p (r + 1) := by
  funext i
  change (if i = cell B (p + r - 1) _ then some (bit x w r)
    else if i.val = p + r then none else rollCell x w p r i.val) =
      rollCell x w p (r + 1) i.val
  unfold rollCell
  by_cases h0 : i.val = p + r - 1
  · have he : i = cell B (p + r - 1) (by rw [pair_eq]; omega) := Fin.ext h0
    rw [if_pos he, if_neg (by omega), if_pos (by omega)]
    congr 2
    omega
  · have he : i ≠ cell B (p + r - 1) (by rw [pair_eq]; omega) :=
      fun h => h0 (congrArg Fin.val h)
    rw [if_neg he]
    by_cases h1 : i.val = p + r
    · rw [if_pos h1, if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    · rw [if_neg h1]
      by_cases ha : i.val < p - 1
      · rw [if_pos ha, if_pos ha]
      · rw [if_neg ha, if_neg ha]
        by_cases hb : i.val < p - 1 + r
        · rw [if_pos hb, if_pos (by omega)]
        · rw [if_neg hb, if_neg (by omega)]
          by_cases hc : i.val < p + r
          · have hv : i.val = p + r - 1 := by omega
            exact absurd hv h0
          · rw [if_neg (show ¬i.val < p - 1 + (r + 1) by omega),
              if_neg (show ¬i.val < p + (r + 1) by omega)]

private def takeState (r : Nat) : Fin alignmentStateCount :=
  if r = 0 then qShiftTake else qShiftInspect

private def takeConfig {n m : Nat} (B : Nat) (x : Bitstring n)
    (w : Bitstring m) (p r : Nat) (hp : p ≤ n)
    (hr : r ≤ K n m) : Config alignmentStateCount (pairLength n m) B where
  state := takeState r
  head := cell B (p + r) (by rw [pair_eq]; omega)
  tape := rollTape B x w p r

private def putConfig {n m : Nat} (B : Nat) (x : Bitstring n)
    (w : Bitstring m) (p r : Nat) (hp : p ≤ n) (hpos : 0 < p)
    (hr : r < K n m) : Config alignmentStateCount (pairLength n m) B where
  state := putState (bit x w r)
  head := cell B (p + r - 1) (by rw [pair_eq]; omega)
  tape := takenTape B x w p r

private def gapConfig {n m : Nat} (B : Nat) (x : Bitstring n)
    (w : Bitstring m) (p r : Nat) (hp : p ≤ n) (hpos : 0 < p)
    (hr : r ≤ K n m) : Config alignmentStateCount (pairLength n m) B where
  state := qShiftGap
  head := cell B (p + r - 1) (by rw [pair_eq]; omega)
  tape := rollTape B x w p r

private theorem take_read {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {p r : Nat} (hp : p ≤ n) (hpos : 0 < p) (hr : r < K n m) :
    (takeConfig B x w p r hp (by omega)).tape
      (takeConfig B x w p r hp (by omega)).head = some (bit x w r) := by
  change rollCell x w p r (p + r) = _
  unfold rollCell
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos (by omega), show p + r - p = r by omega]

private theorem put_read {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {p r : Nat} (hp : p ≤ n) (hpos : 0 < p) (hr : r < K n m) :
    (putConfig B x w p r hp hpos hr).tape
      (putConfig B x w p r hp hpos hr).head = none := by
  change (if p + r - 1 = p + r then none
    else rollCell x w p r (p + r - 1)) = none
  rw [if_neg (by omega)]
  unfold rollCell
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]

private theorem gap_read {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {p r : Nat} (hp : p ≤ n) (hpos : 0 < p) (hr0 : 0 < r)
    (hr : r ≤ K n m) :
    (gapConfig B x w p r hp hpos hr).tape
      (gapConfig B x w p r hp hpos hr).head = none := by
  change rollCell x w p r (p + r - 1) = none
  unfold rollCell
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]

private theorem take_action (r : Nat) (b : Bool) :
    machine.step (takeState r) (some b) = (putState b, none, .left) := by
  by_cases h : r = 0
  · subst r
    cases b <;> rfl
  · have hs : takeState r = qShiftInspect := by simp [takeState, h]
    rw [hs]
    cases b <;> rfl

private theorem put_action (b : Bool) :
    machine.step (putState b) none = (qShiftGap, some b, .right) := by
  cases b <;> rfl

private theorem step_take {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {p r : Nat} (hp : p ≤ n) (hpos : 0 < p) (hr : r < K n m) :
    machine.stepConfig (takeConfig B x w p r hp (by omega)) =
      putConfig B x w p r hp hpos hr := by
  rw [stepConfig_eq _ _ _ _ (by rw [take_read x w hp hpos hr]; exact take_action _ _)]
  apply config_ext
  · rfl
  · apply Fin.ext
    change p + r - 1 = p + r - 1
    rfl
  · exact erase_source x w hp hr

private theorem step_put {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {p r : Nat} (hp : p ≤ n) (hpos : 0 < p) (hr : r < K n m) :
    machine.stepConfig (putConfig B x w p r hp hpos hr) =
      gapConfig B x w p (r + 1) hp hpos (by omega) := by
  rw [stepConfig_eq _ _ _ _ (by rw [put_read x w hp hpos hr]; exact put_action _)]
  apply config_ext
  · rfl
  · apply Fin.ext
    rw [move_right_val _ (by
      change (p + r - 1) + 1 < tapeLength (pairLength n m) B
      unfold tapeLength
      rw [pair_eq]
      omega)]
    change (p + r - 1) + 1 = p + (r + 1) - 1
    omega
  · exact fill_hole x w hp hpos hr

private theorem step_gap {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {p r : Nat} (hp : p ≤ n) (hpos : 0 < p) (hr0 : 0 < r)
    (hr : r ≤ K n m) :
    machine.stepConfig (gapConfig B x w p r hp hpos hr) =
      takeConfig B x w p r hp hr := by
  rw [stepConfig_eq _ _ _ _ (by rw [gap_read x w hp hpos hr0 hr]; rfl)]
  apply config_ext
  · change qShiftInspect = takeState r
    rw [show takeState r = qShiftInspect by simp [takeState, Nat.ne_of_gt hr0]]
  · apply Fin.ext
    rw [move_right_val _ (by
      change (p + r - 1) + 1 < tapeLength (pairLength n m) B
      unfold tapeLength
      rw [pair_eq]
      omega)]
    change (p + r - 1) + 1 = p + r
    omega
  · change (fun i => if i = (gapConfig B x w p r hp hpos hr).head then none
      else rollTape B x w p r i) = rollTape B x w p r
    funext i
    by_cases hi : i = (gapConfig B x w p r hp hpos hr).head
    · rw [if_pos hi]
      subst i
      exact (gap_read (B := B) x w hp hpos hr0 hr).symm
    · rw [if_neg hi]

private theorem copy_round {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {p r : Nat} (hp : p ≤ n) (hpos : 0 < p) (hr : r < K n m) :
    machine.run 3 (takeConfig B x w p r hp (by omega)) =
      takeConfig B x w p (r + 1) hp (by omega) := by
  change machine.stepConfig (machine.stepConfig (machine.stepConfig _)) = _
  simp only [UniformTM.run]
  rw [step_take x w hp hpos hr, step_put x w hp hpos hr,
    step_gap x w hp hpos (by omega) (by omega)]

private theorem copy_prefix {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {p : Nat} (hp : p ≤ n) (hpos : 0 < p) (r : Nat) (hr : r ≤ K n m) :
    machine.run (3 * r) (takeConfig B x w p 0 hp (by omega)) =
      takeConfig B x w p r hp hr := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [show 3 * (r + 1) = 3 * r + 3 by ring, machine.run_add,
        ih (by omega), copy_round x w hp hpos (by omega)]

private def backConfig {n m : Nat} (B : Nat) (x : Bitstring n)
    (w : Bitstring m) (p : Nat) (hp : p ≤ n) :
    Config alignmentStateCount (pairLength n m) B where
  state := qShiftBack
  head := cell B (p + K n m - 1) (by rw [pair_eq]; omega)
  tape := rollTape B x w p (K n m)

private theorem take_last_read {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {p : Nat} (hp : p ≤ n) :
    (takeConfig B x w p (K n m) hp (le_refl _)).tape
      (takeConfig B x w p (K n m) hp (le_refl _)).head = none := by
  change rollCell x w p (K n m) (p + K n m) = none
  unfold rollCell
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

private theorem inspect_none :
    machine.step qShiftInspect none = (qShiftBack, none, .left) := rfl

private theorem step_take_last {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {p : Nat} (hp : p ≤ n) :
    machine.stepConfig (takeConfig B x w p (K n m) hp (le_refl _)) =
      backConfig B x w p hp := by
  rw [stepConfig_eq _ _ _ _ (by rw [take_last_read x w hp]; exact inspect_none)]
  apply config_ext
  · rfl
  · apply Fin.ext
    rfl
  · change (fun i => if i = _ then none else rollTape B x w p (K n m) i) =
      rollTape B x w p (K n m)
    funext i
    by_cases hi : i = (takeConfig B x w p (K n m) hp (le_refl _)).head
    · rw [if_pos hi]
      subst i
      exact (take_last_read (B := B) x w hp).symm
    · rw [if_neg hi]

private theorem back_read {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {p : Nat} (hp : p ≤ n) (hpos : 0 < p) :
    (backConfig B x w p hp).tape (backConfig B x w p hp).head = none := by
  change rollCell x w p (K n m) (p + K n m - 1) = none
  unfold rollCell
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]

private theorem step_back {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {p : Nat} (hp : p ≤ n) (hpos : 0 < p) :
    machine.stepConfig (backConfig B x w p hp) =
      checkConfig B x w (p - 1) 0 (by omega) (by omega) := by
  rw [stepConfig_eq _ _ _ _ (by rw [back_read x w hp hpos]; rfl)]
  apply config_ext
  · change qCheckAt = checkState 0
    rfl
  · apply Fin.ext
    change p + K n m - 1 - 1 = p - 1 + K n m - 1
    omega
  · change (fun i => if i = _ then none else rollTape B x w p (K n m) i) =
      blockTape B x w (p - 1)
    rw [roll_last x w]
    funext i
    by_cases hi : i = (backConfig B x w p hp).head
    · rw [if_pos hi]
      subst i
      exact (block_blank x w (B := B) (p := p - 1) (k := p + K n m - 1)
        (Or.inr (by omega)) _ rfl).symm
    · rw [if_neg hi]

private theorem shift_all {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {p : Nat} (hp : p ≤ n) (hpos : 0 < p) :
    machine.run (3 * K n m + 3) (checkConfig B x w p (K n m) hp (le_refl _)) =
      checkConfig B x w (p - 1) 0 (by omega) (by omega) := by
  rw [show 3 * K n m + 3 = 1 + 3 * K n m + 2 by omega, machine.run_add]
  have hblank := block_blank x w (B := B) (p := p) (k := p - 1)
    (Or.inl (by omega)) (checkConfig B x w p (K n m) hp (le_refl _)).head
      (by change p + K n m - 1 - K n m = p - 1; omega)
  have hfirst : machine.stepConfig (checkConfig B x w p (K n m) hp (le_refl _)) =
      takeConfig B x w p 0 hp (by omega) := by
    have ha : machine.step
        (checkConfig B x w p (K n m) hp (le_refl _)).state
        ((checkConfig B x w p (K n m) hp (le_refl _)).tape
          (checkConfig B x w p (K n m) hp (le_refl _)).head) =
        (qShiftTake, none, .right) := by
      change machine.step qCheckNext
        (blockTape B x w p (checkConfig B x w p (K n m) hp (le_refl _)).head) = _
      rw [hblank]
      rfl
    rw [stepConfig_eq _ _ _ _ ha]
    apply config_ext
    · change qShiftTake = takeState 0
      rfl
    · apply Fin.ext
      rw [move_right_val _ (by
        change p + K n m - 1 - K n m + 1 < tapeLength (pairLength n m) B
        unfold tapeLength
        rw [pair_eq]
        omega)]
      change p + K n m - 1 - K n m + 1 = p + 0
      omega
    · change (fun i => if i = _ then none else blockTape B x w p i) =
        rollTape B x w p 0
      rw [roll_zero x w hpos]
      funext i
      by_cases hi : i = (checkConfig B x w p (K n m) hp (le_refl _)).head
      · rw [if_pos hi]
        subst i
        exact hblank.symm
      · rw [if_neg hi]
  rw [show 1 + 3 * K n m = 1 + 3 * K n m from rfl, machine.run_add,
    show machine.run 1 (checkConfig B x w p (K n m) hp (le_refl _)) =
      takeConfig B x w p 0 hp (by omega) by exact hfirst,
    copy_prefix x w hp hpos (K n m) (le_refl _)]
  change machine.stepConfig (machine.stepConfig _) = _
  simp only [UniformTM.run]
  rw [step_take_last x w hp, step_back x w hp hpos]

private theorem full_round {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {p : Nat} (hp : p ≤ n) (hpos : 0 < p) :
    machine.run (10 * K n m + 3) (checkConfig B x w p 0 hp (by omega)) =
      checkConfig B x w (p - 1) 0 (by omega) (by omega) := by
  rw [show 10 * K n m + 3 = 7 * K n m + (3 * K n m + 3) by ring,
    machine.run_add, scan_prefix x w hp (K n m) (le_refl _) (Or.inl hpos),
    shift_all x w hp hpos]

private theorem run_rounds {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    (p : Nat) (hp : p ≤ n) :
    machine.run (p * (10 * K n m + 3))
      (checkConfig B x w p 0 hp (by omega)) =
        checkConfig B x w 0 0 (by omega) (by omega) := by
  induction p with
  | zero =>
      simp only [Nat.zero_mul, UniformTM.run]
  | succ p ih =>
      rw [show (p + 1) * (10 * K n m + 3) =
          (10 * K n m + 3) + p * (10 * K n m + 3) by ring,
        machine.run_add, full_round x w hp (by omega)]
      simpa only [Nat.add_sub_cancel] using ih (by omega)

private theorem run_from_check {n m B : Nat} (x : Bitstring n) (w : Bitstring m) :
    machine.run (n * (10 * K n m + 3) + (7 * (K n m - 1) + 5))
      (checkConfig B x w n 0 (le_refl _) (by omega)) = finalConfig B x w := by
  rw [machine.run_add, run_rounds x w n (le_refl _), final_scan x w]

private def sourceHead (n m B : Nat) : Fin (tapeLength (pairLength n m) B) :=
  if h : B = 0 then ⟨pairLength n m, by unfold tapeLength; omega⟩
  else ⟨pairLength n m + 1, by
    have := Nat.one_le_iff_ne_zero.mpr h
    unfold tapeLength
    omega⟩

private def sourceConfig {n m : Nat} (B : Nat) (x : Bitstring n)
    (w : Bitstring m) : Config alignmentStateCount (pairLength n m) B where
  state := qStart
  head := sourceHead n m B
  tape := blockTape B x w n

private theorem start_source {n m B : Nat} (x : Bitstring n) (w : Bitstring m) :
    startConfig B x w = sourceConfig B x w := by
  apply config_ext
  · rfl
  · apply Fin.ext
    have h := (FixedPairOriginShiftBootstrap.final_fields (B := B) x w).2.2.1
    rw [FixedPairOriginShiftBootstrap.run_exact] at h
    change (FixedPairOriginShiftBootstrap.finalConfig B x w).head.val =
      (sourceHead n m B).val
    rw [h]
    cases B <;> simp [sourceHead]
  · exact bootstrap_tape x w

private def normConfig {n m : Nat} (B : Nat) (x : Bitstring n)
    (w : Bitstring m) : Config alignmentStateCount (pairLength n m) B where
  state := qNormalize
  head := cell B (pairLength n m + Nat.min B 1 - 1)
    (by cases B <;> simp)
  tape := blockTape B x w n

private def entryConfig {n m : Nat} (B : Nat) (x : Bitstring n)
    (w : Bitstring m) : Config alignmentStateCount (pairLength n m) B where
  state := qCheckAt
  head := cell B (if B = 0 then pairLength n m else pairLength n m - 1)
    (by split <;> omega)
  tape := blockTape B x w n

private theorem source_read {n m B : Nat} (x : Bitstring n) (w : Bitstring m) :
    (sourceConfig B x w).tape (sourceConfig B x w).head = none := by
  cases B with
  | zero =>
      change blockCell x w n (pairLength n m) = none
      unfold blockCell
      rw [if_neg (by rw [pair_eq]; omega)]
  | succ B =>
      change blockCell x w n (pairLength n m + 1) = none
      unfold blockCell
      rw [if_neg (by rw [pair_eq]; omega)]

private theorem step_source {n m B : Nat} (x : Bitstring n) (w : Bitstring m) :
    machine.stepConfig (sourceConfig B x w) = normConfig B x w := by
  rw [stepConfig_eq _ _ _ _ (by rw [source_read x w]; rfl)]
  apply config_ext
  · rfl
  · apply Fin.ext
    cases B with
    | zero =>
        change pairLength n m - 1 = pairLength n m + Nat.min 0 1 - 1
        simp
    | succ B =>
        change pairLength n m + 1 - 1 =
          pairLength n m + Nat.min (B + 1) 1 - 1
        simp
  · change (fun i => if i = _ then none else blockTape B x w n i) = _
    funext i
    by_cases hi : i = (sourceConfig B x w).head
    · rw [if_pos hi]
      subst i
      exact (source_read (B := B) x w).symm
    · rw [if_neg hi]
      rfl

private theorem norm_read {n m B : Nat} (x : Bitstring n) (w : Bitstring m) :
    (normConfig B x w).tape (normConfig B x w).head =
      if B = 0 then some true else none := by
  cases B with
  | zero =>
      change blockCell x w n (pairLength n m + Nat.min 0 1 - 1) = some true
      simp only [Nat.zero_min, Nat.add_zero]
      unfold blockCell
      rw [if_pos (by rw [pair_eq]; unfold K; omega), show pairLength n m - 1 - n =
        n + m by unfold pairLength; omega, bit_marker]
  | succ B =>
      change blockCell x w n (pairLength n m + Nat.min (B + 1) 1 - 1) = none
      simp only [Nat.min_eq_right (by omega : 1 ≤ B + 1), Nat.add_sub_cancel]
      unfold blockCell
      rw [if_neg (by rw [pair_eq]; omega)]

private theorem step_norm {n m B : Nat} (x : Bitstring n) (w : Bitstring m) :
    machine.stepConfig (normConfig B x w) = entryConfig B x w := by
  cases B with
  | zero =>
      rw [stepConfig_eq _ _ _ _ (by rw [norm_read x w]; rfl)]
      apply config_ext
      · rfl
      · apply Fin.ext
        rw [move_right_val _ (by
          change pairLength n m - 1 + 1 < tapeLength (pairLength n m) 0
          unfold tapeLength pairLength
          omega)]
        change pairLength n m - 1 + 1 =
          (cell 0 (if 0 = 0 then pairLength n m else pairLength n m - 1)
            (by simp)).val
        simp only [cell_val]
        simp
        unfold pairLength
        omega
      · change (fun i => if i = _ then some true else blockTape 0 x w n i) = _
        funext i
        by_cases hi : i = (normConfig 0 x w).head
        · rw [if_pos hi]
          subst i
          exact (norm_read (B := 0) x w).symm
        · rw [if_neg hi]
          rfl
  | succ B =>
      rw [stepConfig_eq _ _ _ _ (by rw [norm_read x w]; rfl)]
      apply config_ext
      · rfl
      · apply Fin.ext
        change pairLength n m + Nat.min (B + 1) 1 - 1 - 1 =
          if B + 1 = 0 then pairLength n m else pairLength n m - 1
        simp
      · change (fun i => if i = _ then none else blockTape (B + 1) x w n i) = _
        funext i
        by_cases hi : i = (normConfig (B + 1) x w).head
        · rw [if_pos hi]
          subst i
          exact (norm_read (B := B + 1) x w).symm
        · rw [if_neg hi]
          rfl

private theorem step_entry {n m B : Nat} (x : Bitstring n) (w : Bitstring m) :
    machine.stepConfig (entryConfig B x w) =
      saveConfig B x w n 0 (le_refl _) (by unfold K; omega) := by
  rw [stepConfig_eq _ _ _ _ (checkAt_action _)]
  apply config_ext
  · rfl
  · apply Fin.ext
    cases B with
    | zero =>
        have hb : ¬(entryConfig 0 x w).head.val + 1 <
            tapeLength (pairLength n m) 0 := by
          change ¬pairLength n m + 1 < pairLength n m + 0 + 1
          omega
        unfold moveHead
        rw [dif_neg hb]
        change pairLength n m = n + K n m
        exact pair_eq n m
    | succ B =>
        rw [move_right_val _ (by
          change pairLength n m - 1 + 1 < tapeLength (pairLength n m) (B + 1)
          unfold tapeLength pairLength
          omega)]
        change pairLength n m - 1 + 1 = n + K n m
        rw [← pair_eq]
        unfold pairLength
        omega
  · change (fun i => if i = (entryConfig B x w).head then
      blockTape B x w n (entryConfig B x w).head else blockTape B x w n i) =
      blockTape B x w n
    funext i
    by_cases hi : i = (entryConfig B x w).head
    · rw [if_pos hi, hi]
    · rw [if_neg hi]

private theorem entry_three {n m B : Nat} (x : Bitstring n) (w : Bitstring m) :
    machine.run 3 (startConfig B x w) =
      saveConfig B x w n 0 (le_refl _) (by unfold K; omega) := by
  simp only [UniformTM.run]
  rw [start_source x w, step_source x w, step_norm x w, step_entry x w]

theorem run_exact {n m : Nat} (B : Nat) (x : Bitstring n) (w : Bitstring m) :
    machine.run (clock n m) (startConfig B x w) = finalConfig B x w := by
  have hc : clock n m = 2 +
      (n * (10 * K n m + 3) + (7 * (K n m - 1) + 5)) := by
    unfold clock K
    rw [show n + m + 1 - 1 = n + m by omega]
    ring
  rw [hc, machine.run_add]
  have he : machine.run 2 (startConfig B x w) = entryConfig B x w := by
    simp only [UniformTM.run]
    rw [start_source x w, step_source x w, step_norm x w]
  rw [he]
  rw [show n * (10 * K n m + 3) + (7 * (K n m - 1) + 5) =
      1 + (n * (10 * K n m + 3) + (7 * (K n m - 1) + 4)) by
      unfold K; omega, machine.run_add]
  rw [show machine.run 1 (entryConfig B x w) =
      saveConfig B x w n 0 (le_refl _) (by unfold K; omega) by
      exact step_entry x w]
  have hs := run_from_check (B := B) x w
  rw [show n * (10 * K n m + 3) + (7 * (K n m - 1) + 5) =
      1 + (n * (10 * K n m + 3) + (7 * (K n m - 1) + 4)) by
      unfold K; omega, machine.run_add] at hs
  have hstep : machine.run 1 (checkConfig B x w n 0 (le_refl _) (by omega)) =
      saveConfig B x w n 0 (le_refl _) (by unfold K; omega) :=
    step_check x w (le_refl n) (by unfold K; omega)
  rw [hstep] at hs
  exact hs

/-! ## Dependency-closed trace and safety surface -/

private def R (n m : Nat) : Nat := 10 * K n m + 3

private def phaseStart (n m k : Nat) : Nat := 3 + k * R n m

private theorem clock_phase (n m : Nat) :
    clock n m = phaseStart n m n + (7 * (K n m - 1) + 4) := by
  unfold clock phaseStart R K
  rw [show n + m + 1 - 1 = n + m by omega]
  ring

private theorem run_one {N B t : Nat}
    (c : Config alignmentStateCount N B) :
    machine.run (t + 1) c = machine.stepConfig (machine.run t c) := by
  rw [show t + 1 = t + 1 from rfl, machine.run_add]
  rfl

private theorem save_round {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {p : Nat} (hp : p ≤ n) (hpos : 0 < p) :
    machine.run (R n m)
        (saveConfig B x w p 0 hp (by unfold K; omega)) =
      saveConfig B x w (p - 1) 0 (by omega) (by unfold K; omega) := by
  have hf := full_round (B := B) x w hp hpos
  have hs := step_check (B := B) x w (p := p) (j := 0) hp
    (by unfold K; omega)
  have hs' := step_check (B := B) x w (p := p - 1) (j := 0)
    (by omega) (by unfold K; omega)
  calc
    machine.run (R n m) (saveConfig B x w p 0 hp _) =
        machine.run (R n m)
          (machine.run 1 (checkConfig B x w p 0 hp (by omega))) := by
            simpa only [UniformTM.run] using
              congrArg (machine.run (R n m)) hs.symm
    _ = machine.run (1 + R n m) (checkConfig B x w p 0 hp (by omega)) := by
          rw [machine.run_add]
    _ = machine.run (R n m + 1) (checkConfig B x w p 0 hp (by omega)) := by
          rw [Nat.add_comm 1 (R n m)]
    _ = machine.run 1
        (machine.run (R n m) (checkConfig B x w p 0 hp (by omega))) := by
          rw [machine.run_add]
    _ = machine.run 1 (checkConfig B x w (p - 1) 0 (by omega) (by omega)) := by
          rw [show R n m = 10 * K n m + 3 by rfl, hf]
    _ = saveConfig B x w (p - 1) 0 (by omega) (by unfold K; omega) := hs'

private theorem run_save {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    (k : Nat) (hk : k ≤ n) :
    machine.run (phaseStart n m k) (startConfig B x w) =
      saveConfig B x w (n - k) 0 (by omega) (by unfold K; omega) := by
  induction k with
  | zero => simpa [phaseStart] using entry_three (B := B) x w
  | succ k ih =>
      rw [show phaseStart n m (k + 1) =
          phaseStart n m k + R n m by unfold phaseStart; ring, machine.run_add,
        ih (by omega)]
      simpa only [show n - k - 1 = n - (k + 1) by omega] using
        save_round (B := B) x w (p := n - k) (by omega) (by omega)

private theorem run_save_scan {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {p j : Nat} (hp : p ≤ n) (hj : j < K n m)
    (hstop : 0 < p ∨ j ≤ K n m - 1) :
    machine.run (7 * j)
        (saveConfig B x w p 0 hp (by unfold K; omega)) =
      saveConfig B x w p j hp hj := by
  have hscan := scan_prefix (B := B) x w hp j (by omega) hstop
  have h0 := step_check (B := B) x w (p := p) (j := 0) hp
    (by unfold K; omega)
  have hj' := step_check (B := B) x w (p := p) (j := j) hp hj
  have h : machine.run (7 * j + 1)
      (checkConfig B x w p 0 hp (by omega)) = saveConfig B x w p j hp hj := by
    rw [machine.run_add, hscan]
    exact hj'
  calc
    machine.run (7 * j) (saveConfig B x w p 0 hp _) =
        machine.run (7 * j)
          (machine.run 1 (checkConfig B x w p 0 hp (by omega))) := by
            simpa only [UniformTM.run] using
              congrArg (machine.run (7 * j)) h0.symm
    _ = saveConfig B x w p j hp hj := by
      rw [← machine.run_add, show 1 + 7 * j = 7 * j + 1 by omega]
      exact h

private theorem run_scan_phases {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {p j : Nat} (hp : p ≤ n) (hj : j < K n m)
    (hstop : 0 < p ∨ j ≤ K n m - 1)
    (hcell : 0 < p + K n m - 1 - j) :
    let c := saveConfig B x w p 0 hp (by unfold K; omega)
    machine.run (7 * j) c = saveConfig B x w p j hp hj ∧
    machine.run (7 * j + 1) c = tryConfig B x w p j hp hj ∧
    machine.run (7 * j + 2) c = bounceConfig B x w p j hp hj ∧
    machine.run (7 * j + 3) c = classConfig B x w p j hp hj ∧
    machine.run (7 * j + 4) c = restoreConfig B x w p j hp hj ∧
    machine.run (7 * j + 5) c = leftConfig B x w p j hp hj ∧
    machine.run (7 * j + 6) c =
      checkConfig B x w p (j + 1) hp (by omega) := by
  dsimp
  have h0 := run_save_scan (B := B) x w hp hj hstop
  refine ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [run_one, h0, step_save x w hp hj]
  · rw [run_one, run_one, h0, step_save x w hp hj, step_try x w hp hj]
  · rw [run_one, run_one, run_one, h0, step_save x w hp hj,
      step_try x w hp hj, step_bounce x w hp hj hcell]
  · rw [run_one, run_one, run_one, run_one, h0, step_save x w hp hj,
      step_try x w hp hj, step_bounce x w hp hj hcell,
      step_class x w hp hj hcell]
  · rw [run_one, run_one, run_one, run_one, run_one, h0,
      step_save x w hp hj, step_try x w hp hj,
      step_bounce x w hp hj hcell, step_class x w hp hj hcell,
      step_restore x w hp hj]
  · rw [run_one, run_one, run_one, run_one, run_one, run_one, h0,
      step_save x w hp hj, step_try x w hp hj,
      step_bounce x w hp hj hcell, step_class x w hp hj hcell,
      step_restore x w hp hj, step_left x w hp hj hcell]

private theorem step_shift_start {n m B : Nat} (x : Bitstring n)
    (w : Bitstring m) {p : Nat} (hp : p ≤ n) (hpos : 0 < p) :
    machine.stepConfig (checkConfig B x w p (K n m) hp (le_refl _)) =
      takeConfig B x w p 0 hp (by omega) := by
  have hblank := block_blank x w (B := B) (p := p) (k := p - 1)
    (Or.inl (by omega)) (checkConfig B x w p (K n m) hp (le_refl _)).head
      (by change p + K n m - 1 - K n m = p - 1; omega)
  have ha : machine.step
      (checkConfig B x w p (K n m) hp (le_refl _)).state
      ((checkConfig B x w p (K n m) hp (le_refl _)).tape
        (checkConfig B x w p (K n m) hp (le_refl _)).head) =
      (qShiftTake, none, .right) := by
    change machine.step qCheckNext
      (blockTape B x w p (checkConfig B x w p (K n m) hp (le_refl _)).head) = _
    rw [hblank]
    rfl
  rw [stepConfig_eq _ _ _ _ ha]
  apply config_ext
  · rfl
  · apply Fin.ext
    rw [move_right_val _ (by
      change p + K n m - 1 - K n m + 1 < tapeLength (pairLength n m) B
      unfold tapeLength
      rw [pair_eq]
      omega)]
    change p + K n m - 1 - K n m + 1 = p + 0
    omega
  · change (fun i => if i = _ then none else blockTape B x w p i) =
      rollTape B x w p 0
    rw [roll_zero x w hpos]
    funext i
    by_cases hi : i = (checkConfig B x w p (K n m) hp (le_refl _)).head
    · rw [if_pos hi]
      subst i
      exact hblank.symm
    · rw [if_neg hi]

private theorem run_check_last {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {p : Nat} (hp : p ≤ n) (hpos : 0 < p) :
    machine.run (7 * K n m - 1)
        (saveConfig B x w p 0 hp (by unfold K; omega)) =
      checkConfig B x w p (K n m) hp (le_refl _) := by
  have h := (run_scan_phases (B := B) x w (p := p) (j := K n m - 1)
    (hp := hp) (hj := by unfold K; omega) (hstop := Or.inl hpos)
    (hcell := by unfold K; omega)).2.2.2.2.2.2
  simpa only [show 7 * (K n m - 1) + 6 = 7 * K n m - 1 by
    unfold K; omega] using h

private theorem run_take_shift {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {p r : Nat} (hp : p ≤ n) (hpos : 0 < p) (hr : r ≤ K n m) :
    machine.run (7 * K n m + 3 * r)
        (saveConfig B x w p 0 hp (by unfold K; omega)) =
      takeConfig B x w p r hp hr := by
  rw [show 7 * K n m + 3 * r = (7 * K n m - 1) + (1 + 3 * r) by
      unfold K; omega, machine.run_add, run_check_last x w hp hpos,
    machine.run_add]
  simp only [UniformTM.run]
  rw [step_shift_start (B := B) x w hp hpos, copy_prefix x w hp hpos r hr]

private theorem run_shift_phases {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {p r : Nat} (hp : p ≤ n) (hpos : 0 < p) (hr : r < K n m) :
    let c := saveConfig B x w p 0 hp (by unfold K; omega)
    machine.run (7 * K n m + 3 * r) c = takeConfig B x w p r hp (by omega) ∧
    machine.run (7 * K n m + 3 * r + 1) c = putConfig B x w p r hp hpos hr ∧
    machine.run (7 * K n m + 3 * r + 2) c =
      gapConfig B x w p (r + 1) hp hpos (by omega) := by
  dsimp
  have h0 := run_take_shift (B := B) x w hp hpos (show r ≤ K n m by omega)
  refine ⟨h0, ?_, ?_⟩
  · rw [run_one, h0, step_take x w hp hpos hr]
  · rw [run_one, run_one, h0, step_take x w hp hpos hr,
      step_put x w hp hpos hr]

private theorem run_shift_tail {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {p : Nat} (hp : p ≤ n) (hpos : 0 < p) :
    let c := saveConfig B x w p 0 hp (by unfold K; omega)
    machine.run (10 * K n m + 1) c = backConfig B x w p hp ∧
    machine.run (10 * K n m + 2) c =
      checkConfig B x w (p - 1) 0 (by omega) (by omega) := by
  dsimp
  have htake := run_take_shift (B := B) x w hp hpos (le_refl (K n m))
  refine ⟨?_, ?_⟩
  · rw [show 10 * K n m + 1 = (7 * K n m + 3 * K n m) + 1 by ring,
      run_one, htake, step_take_last x w hp]
  · rw [show 10 * K n m + 2 = (7 * K n m + 3 * K n m) + 2 by ring,
      run_one, run_one, htake, step_take_last x w hp, step_back x w hp hpos]

private theorem run_final_save {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {j : Nat} (hj : j < K n m) :
    machine.run (7 * j)
        (saveConfig B x w 0 0 (by omega) (by unfold K; omega)) =
      saveConfig B x w 0 j (by omega) hj := by
  exact run_save_scan x w (by omega) hj (Or.inr (by omega))

private theorem run_final_scan_phases {n m B : Nat} (x : Bitstring n)
    (w : Bitstring m) {j : Nat} (hj : j < K n m - 1) :
    let c := saveConfig B x w 0 0 (by omega) (by unfold K; omega)
    machine.run (7 * j) c = saveConfig B x w 0 j (by omega) (by omega) ∧
    machine.run (7 * j + 1) c = tryConfig B x w 0 j (by omega) (by omega) ∧
    machine.run (7 * j + 2) c = bounceConfig B x w 0 j (by omega) (by omega) ∧
    machine.run (7 * j + 3) c = classConfig B x w 0 j (by omega) (by omega) ∧
    machine.run (7 * j + 4) c = restoreConfig B x w 0 j (by omega) (by omega) ∧
    machine.run (7 * j + 5) c = leftConfig B x w 0 j (by omega) (by omega) ∧
    machine.run (7 * j + 6) c =
      checkConfig B x w 0 (j + 1) (by omega) (by omega) := by
  exact run_scan_phases x w (by omega) (by unfold K at *; omega)
    (Or.inr (by omega)) (by omega)

private theorem run_final_tail {n m B : Nat} (x : Bitstring n) (w : Bitstring m) :
    let c := saveConfig B x w 0 0 (by omega) (by unfold K; omega)
    machine.run (7 * (K n m - 1)) c =
        saveConfig B x w 0 (K n m - 1) (by omega) (by unfold K; omega) ∧
    machine.run (7 * (K n m - 1) + 1) c =
        tryConfig B x w 0 (K n m - 1) (by omega) (by unfold K; omega) ∧
    machine.run (7 * (K n m - 1) + 2) c =
        bounceConfig B x w 0 (K n m - 1) (by omega) (by unfold K; omega) ∧
    machine.run (7 * (K n m - 1) + 3) c = originClassConfig B x w ∧
    machine.run (7 * (K n m - 1) + 4) c = finalConfig B x w := by
  dsimp
  have h0 := run_final_save (B := B) x w
    (show K n m - 1 < K n m by unfold K; omega)
  refine ⟨h0, ?_, ?_, ?_, ?_⟩
  · rw [run_one, h0, step_save x w (by omega) (by unfold K; omega)]
  · rw [run_one, run_one, h0, step_save x w (by omega) (by unfold K; omega),
      step_try x w (by omega) (by unfold K; omega)]
  · rw [run_one, run_one, run_one, h0,
      step_save x w (by omega) (by unfold K; omega),
      step_try x w (by omega) (by unfold K; omega), step_bounce_origin x w]
  · rw [run_one, run_one, run_one, run_one, h0,
      step_save x w (by omega) (by unfold K; omega),
      step_try x w (by omega) (by unfold K; omega), step_bounce_origin x w,
      step_origin x w]

private theorem phaseStart_succ (n m k : Nat) :
    phaseStart n m (k + 1) = phaseStart n m k + R n m := by
  unfold phaseStart
  ring

private theorem phaseStart_decompose (n m s : Nat) (hs : 3 ≤ s) :
    ∃ k d, d < R n m ∧ s = phaseStart n m k + d := by
  induction s with
  | zero => omega
  | succ s ih =>
      by_cases hs3 : s < 3
      · have he : s = 2 := by omega
        subst s
        exact ⟨0, 0, by unfold R K; omega, by simp [phaseStart]⟩
      · obtain ⟨k, d, hd, he⟩ := ih (by omega)
        by_cases hd' : d + 1 < R n m
        · exact ⟨k, d + 1, hd', by omega⟩
        · refine ⟨k + 1, 0, by unfold R K; omega, ?_⟩
          rw [phaseStart_succ]
          omega

private theorem phase_index_le {n m s k d : Nat} (hs : s ≤ clock n m)
    (he : s = phaseStart n m k + d) : k ≤ n := by
  by_contra hn
  have hkn : n + 1 ≤ k := by omega
  have hmul := Nat.mul_le_mul_right (R n m) hkn
  have htail : 7 * (K n m - 1) + 4 < R n m := by
    unfold R K
    omega
  have hclock := clock_phase n m
  have hdist : (n + 1) * R n m = n * R n m + R n m := by ring
  rw [hdist] at hmul
  have hphase : phaseStart n m (n + 1) ≤ s := by
    unfold phaseStart at he ⊢
    omega
  have hclocklt : clock n m < phaseStart n m (n + 1) := by
    rw [hclock, phaseStart_succ]
    omega
  omega

private theorem mod_seven (t : Nat) : ∃ r d, d ≤ 6 ∧ t = 7 * r + d := by
  refine ⟨t / 7, t % 7, ?_, ?_⟩
  · have h := Nat.mod_lt t (by decide : 0 < 7)
    omega
  · have h := Nat.mod_add_div t 7
    omega

private theorem mod_three_local (t : Nat) : ∃ r d, d ≤ 2 ∧ t = 3 * r + d := by
  refine ⟨t / 3, t % 3, ?_, ?_⟩
  · have h := Nat.mod_lt t (by decide : 0 < 3)
    omega
  · have h := Nat.mod_add_div t 3
    omega

private theorem block_above {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {p : Nat} (hp : p ≤ n) (i : Fin (tapeLength (pairLength n m) B))
    (hi : pairLength n m ≤ i.val) : blockTape B x w p i = none := by
  apply block_blank x w (Or.inr (show p + K n m ≤ i.val by
    have he := pair_eq n m
    omega)) i rfl

private theorem clear_above {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {p j : Nat} (hp : p ≤ n) (i : Fin (tapeLength (pairLength n m) B))
    (hi : pairLength n m ≤ i.val) : clearTape B x w p j i = none := by
  change clearCell x w p j i.val = none
  unfold clearCell
  split
  · rfl
  · exact block_above x w hp i hi

private theorem roll_above {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {p r : Nat} (hp : p ≤ n) (hr : r ≤ K n m)
    (i : Fin (tapeLength (pairLength n m) B))
    (hi : pairLength n m ≤ i.val) : rollTape B x w p r i = none := by
  change rollCell x w p r i.val = none
  have he := pair_eq n m
  unfold rollCell
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega)]

private theorem taken_above {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {p r : Nat} (hp : p ≤ n) (hr : r ≤ K n m)
    (i : Fin (tapeLength (pairLength n m) B))
    (hi : pairLength n m ≤ i.val) : takenTape B x w p r i = none := by
  change (if i.val = p + r then none else rollCell x w p r i.val) = none
  split
  · rfl
  · exact roll_above x w hp hr i hi

private def SafeSnapshot {n m B : Nat} (s : Nat)
    (c : Config alignmentStateCount (pairLength n m) B) : Prop :=
  c.state ≠ qAccept ∧ c.state ≠ qReject ∧
  c.head.val ≤ pairLength n m + Nat.min B 1 ∧
  (∀ i, pairLength n m ≤ i.val → c.tape i = none) ∧
  ((machine.step c.state (c.tape c.head)).2.2 = .right →
    (s = 2 ∧ B = 0 ∧ c.head.val = pairLength n m) ∨
      c.head.val + 1 < tapeLength (pairLength n m) B) ∧
  ((machine.step c.state (c.tape c.head)).2.2 = .left →
    (s = clock n m - 3 ∧ c.head.val = 0) ∨ 0 < c.head.val)

private theorem check_action {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {p j : Nat} (hp : p ≤ n) (hj : j ≤ K n m)
    (hlast : j = K n m → 0 < p) :
    (machine.step (checkConfig B x w p j hp hj).state
      ((checkConfig B x w p j hp hj).tape
        (checkConfig B x w p j hp hj).head)).2.2 = .right := by
  by_cases hlt : j < K n m
  · rw [check_read x w hp hlt]
    change (machine.step (checkState j) (some _)).2.2 = .right
    by_cases h0 : j = 0
    · rw [show checkState j = qCheckAt by simp [checkState, h0], checkAt_action]
    · rw [show checkState j = qCheckNext by simp [checkState, h0], checkNext_some]
  · have he : j = K n m := by omega
    subst j
    have hp0 : 0 < p := hlast rfl
    have hb := block_blank x w (B := B) (p := p) (k := p - 1)
      (Or.inl (by omega)) (checkConfig B x w p (K n m) hp hj).head
      (by change p + K n m - 1 - K n m = p - 1; omega)
    change (machine.step (checkState (K n m))
      (blockTape B x w p (checkConfig B x w p (K n m) hp hj).head)).2.2 = .right
    rw [hb]
    rw [show checkState (K n m) = qCheckNext by
      simp [checkState, show K n m ≠ 0 by unfold K; omega]]
    rfl

private theorem safe_check {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {s p j : Nat} (hp : p ≤ n) (hj : j ≤ K n m)
    (hlast : j = K n m → 0 < p) :
    SafeSnapshot s (checkConfig B x w p j hp hj) := by
  unfold SafeSnapshot
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · change checkState j ≠ qAccept
    unfold checkState
    split <;> decide
  · change checkState j ≠ qReject
    unfold checkState
    split <;> decide
  · change p + K n m - 1 - j ≤ pairLength n m + Nat.min B 1
    rw [pair_eq]
    omega
  · exact fun i hi => block_above x w hp i hi
  · rw [check_action x w hp hj hlast]
    intro _
    right
    change p + K n m - 1 - j + 1 < tapeLength (pairLength n m) B
    unfold tapeLength
    rw [pair_eq]
    have hK : 0 < K n m := by unfold K; omega
    by_cases he : j = K n m
    · have := hlast he
      omega
    · omega
  · rw [check_action x w hp hj hlast]
    simp

private theorem safe_save {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {s p j : Nat} (hp : p ≤ n) (hj : j < K n m) :
    SafeSnapshot s (saveConfig B x w p j hp hj) := by
  have hmove : (machine.step (saveConfig B x w p j hp hj).state
      ((saveConfig B x w p j hp hj).tape
        (saveConfig B x w p j hp hj).head)).2.2 = .left := by
    rw [save_read x w hp hj]
    exact congrArg (fun a => a.2.2) (save_action _)
  unfold SafeSnapshot
  rw [hmove]
  refine ⟨?_, ?_, ?_, fun i hi => block_above x w hp i hi,
    by simp, ?_⟩
  · change qCheckSave ≠ qAccept
    decide
  · change qCheckSave ≠ qReject
    decide
  · change p + K n m - j ≤ pairLength n m + Nat.min B 1
    rw [pair_eq]
    omega
  · intro _
    right
    change 0 < p + K n m - j
    unfold K at hj ⊢
    omega

private theorem safe_try {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {s p j : Nat} (hp : p ≤ n) (hj : j < K n m)
    (horigin : p + K n m - 1 - j = 0 → s = clock n m - 3) :
    SafeSnapshot s (tryConfig B x w p j hp hj) := by
  have hmove : (machine.step (tryConfig B x w p j hp hj).state
      ((tryConfig B x w p j hp hj).tape
        (tryConfig B x w p j hp hj).head)).2.2 = .left := by
    rw [try_read x w hp hj]
    exact congrArg (fun a => a.2.2) (try_action _ _)
  unfold SafeSnapshot
  rw [hmove]
  refine ⟨?_, ?_, ?_, fun i hi => clear_above x w hp i hi, by simp, ?_⟩
  · change savedState _ ≠ qAccept
    cases h : blockCell x w p (p + K n m - j) with
    | none => simp [savedState]; decide
    | some b => cases b <;> simp [savedState] <;> decide
  · change savedState _ ≠ qReject
    cases h : blockCell x w p (p + K n m - j) with
    | none => simp [savedState]; decide
    | some b => cases b <;> simp [savedState] <;> decide
  · change p + K n m - 1 - j ≤ pairLength n m + Nat.min B 1
    rw [pair_eq]
    omega
  · intro _
    by_cases h0 : p + K n m - 1 - j = 0
    · left
      exact ⟨horigin h0, h0⟩
    · right
      change 0 < p + K n m - 1 - j
      omega

private theorem safe_bounce {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {s p j : Nat} (hp : p ≤ n) (hj : j < K n m) :
    SafeSnapshot s (bounceConfig B x w p j hp hj) := by
  have hmove : (machine.step (bounceConfig B x w p j hp hj).state
      ((bounceConfig B x w p j hp hj).tape
        (bounceConfig B x w p j hp hj).head)).2.2 = .right := by
    change (machine.step (bounceState _) _).2.2 = .right
    exact congrArg (fun a => a.2.2) (bounce_action _ _)
  unfold SafeSnapshot
  rw [hmove]
  refine ⟨?_, ?_, ?_, fun i hi => clear_above x w hp i hi, ?_, by simp⟩
  · change bounceState _ ≠ qAccept
    cases h : blockCell x w p (p + K n m - j) with
    | none => simp [bounceState]; decide
    | some b => cases b <;> simp [bounceState] <;> decide
  · change bounceState _ ≠ qReject
    cases h : blockCell x w p (p + K n m - j) with
    | none => simp [bounceState]; decide
    | some b => cases b <;> simp [bounceState] <;> decide
  · change p + K n m - 1 - j - 1 ≤ pairLength n m + Nat.min B 1
    rw [pair_eq]
    omega
  · intro _
    right
    change p + K n m - 1 - j - 1 + 1 < tapeLength (pairLength n m) B
    unfold tapeLength
    rw [pair_eq]
    omega

private theorem safe_class {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {s p j : Nat} (hp : p ≤ n) (hj : j < K n m) :
    SafeSnapshot s (classConfig B x w p j hp hj) := by
  have hmove : (machine.step (classConfig B x w p j hp hj).state
      ((classConfig B x w p j hp hj).tape
        (classConfig B x w p j hp hj).head)).2.2 = .right := by
    rw [class_read x w hp hj]
    exact congrArg (fun a => a.2.2) (class_some _ _)
  unfold SafeSnapshot
  rw [hmove]
  refine ⟨?_, ?_, ?_, fun i hi => clear_above x w hp i hi, ?_, by simp⟩
  · change classState _ ≠ qAccept
    cases h : blockCell x w p (p + K n m - j) with
    | none => simp [classState]; decide
    | some b => cases b <;> simp [classState] <;> decide
  · change classState _ ≠ qReject
    cases h : blockCell x w p (p + K n m - j) with
    | none => simp [classState]; decide
    | some b => cases b <;> simp [classState] <;> decide
  · change p + K n m - 1 - j ≤ pairLength n m + Nat.min B 1
    rw [pair_eq]
    omega
  · intro _
    right
    change p + K n m - 1 - j + 1 < tapeLength (pairLength n m) B
    unfold tapeLength
    rw [pair_eq]
    omega

private theorem safe_restore {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {s p j : Nat} (hp : p ≤ n) (hj : j < K n m) :
    SafeSnapshot s (restoreConfig B x w p j hp hj) := by
  have hmove : (machine.step (restoreConfig B x w p j hp hj).state
      ((restoreConfig B x w p j hp hj).tape
        (restoreConfig B x w p j hp hj).head)).2.2 = .left := by
    rw [restore_read x w hp hj]
    exact congrArg (fun a => a.2.2) (restore_action _)
  unfold SafeSnapshot
  rw [hmove]
  refine ⟨?_, ?_, ?_, fun i hi => clear_above x w hp i hi, by simp, ?_⟩
  · change restoreState _ ≠ qAccept
    cases h : blockCell x w p (p + K n m - j) with
    | none => simp [restoreState]; decide
    | some b => cases b <;> simp [restoreState] <;> decide
  · change restoreState _ ≠ qReject
    cases h : blockCell x w p (p + K n m - j) with
    | none => simp [restoreState]; decide
    | some b => cases b <;> simp [restoreState] <;> decide
  · change p + K n m - j ≤ pairLength n m + Nat.min B 1
    rw [pair_eq]
    omega
  · intro _
    right
    change 0 < p + K n m - j
    unfold K at hj ⊢
    omega

private theorem safe_left {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {s p j : Nat} (hp : p ≤ n) (hj : j < K n m)
    (hcell : 0 < p + K n m - 1 - j) :
    SafeSnapshot s (leftConfig B x w p j hp hj) := by
  have hr0 := block_read x w (B := B) (p := p) (k := p + K n m - 1 - j)
    (by omega) (by omega) (leftConfig B x w p j hp hj).head rfl
  have hr : (leftConfig B x w p j hp hj).tape
      (leftConfig B x w p j hp hj).head = some (bit x w (K n m - 1 - j)) := by
    simpa only [show p + K n m - 1 - j - p = K n m - 1 - j by omega] using hr0
  have hmove : (machine.step (leftConfig B x w p j hp hj).state
      ((leftConfig B x w p j hp hj).tape
        (leftConfig B x w p j hp hj).head)).2.2 = .left := by
    rw [hr]
    exact congrArg (fun a => a.2.2) (left_some _)
  unfold SafeSnapshot
  rw [hmove]
  refine ⟨?_, ?_, ?_, fun i hi => block_above x w hp i hi,
    by simp, ?_⟩
  · change qCheckStepLeft ≠ qAccept
    decide
  · change qCheckStepLeft ≠ qReject
    decide
  · change p + K n m - 1 - j ≤ pairLength n m + Nat.min B 1
    rw [pair_eq]
    omega
  · exact fun _ => Or.inr hcell

private theorem safe_take {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {s p r : Nat} (hp : p ≤ n) (hpos : 0 < p) (hr : r ≤ K n m) :
    SafeSnapshot s (takeConfig B x w p r hp hr) := by
  have hmove : (machine.step (takeConfig B x w p r hp hr).state
      ((takeConfig B x w p r hp hr).tape
        (takeConfig B x w p r hp hr).head)).2.2 = .left := by
    by_cases hlt : r < K n m
    · rw [take_read x w hp hpos hlt]
      exact congrArg (fun a => a.2.2) (take_action r _)
    · have he : r = K n m := by omega
      subst r
      rw [take_last_read x w hp]
      exact congrArg (fun a => a.2.2) inspect_none
  unfold SafeSnapshot
  rw [hmove]
  refine ⟨?_, ?_, ?_, fun i hi => roll_above x w hp hr i hi, by simp, ?_⟩
  · change takeState r ≠ qAccept
    unfold takeState
    split <;> decide
  · change takeState r ≠ qReject
    unfold takeState
    split <;> decide
  · change p + r ≤ pairLength n m + Nat.min B 1
    rw [pair_eq]
    omega
  · intro _
    right
    change 0 < p + r
    omega

private theorem safe_put {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {s p r : Nat} (hp : p ≤ n) (hpos : 0 < p) (hr : r < K n m) :
    SafeSnapshot s (putConfig B x w p r hp hpos hr) := by
  have hmove : (machine.step (putConfig B x w p r hp hpos hr).state
      ((putConfig B x w p r hp hpos hr).tape
        (putConfig B x w p r hp hpos hr).head)).2.2 = .right := by
    rw [put_read x w hp hpos hr]
    exact congrArg (fun a => a.2.2) (put_action _)
  unfold SafeSnapshot
  rw [hmove]
  refine ⟨?_, ?_, ?_, fun i hi => taken_above x w hp (by omega) i hi,
    ?_, by simp⟩
  · change putState _ ≠ qAccept
    unfold putState
    split <;> decide
  · change putState _ ≠ qReject
    unfold putState
    split <;> decide
  · change p + r - 1 ≤ pairLength n m + Nat.min B 1
    rw [pair_eq]
    omega
  · intro _
    right
    change p + r - 1 + 1 < tapeLength (pairLength n m) B
    unfold tapeLength
    rw [pair_eq]
    omega

private theorem safe_gap {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {s p r : Nat} (hp : p ≤ n) (hpos : 0 < p) (hr0 : 0 < r)
    (hr : r ≤ K n m) : SafeSnapshot s (gapConfig B x w p r hp hpos hr) := by
  have hmove : (machine.step (gapConfig B x w p r hp hpos hr).state
      ((gapConfig B x w p r hp hpos hr).tape
        (gapConfig B x w p r hp hpos hr).head)).2.2 = .right := by
    rw [gap_read x w hp hpos hr0 hr]
    rfl
  unfold SafeSnapshot
  rw [hmove]
  refine ⟨?_, ?_, ?_, fun i hi => roll_above x w hp hr i hi,
    ?_, by simp⟩
  · change qShiftGap ≠ qAccept
    decide
  · change qShiftGap ≠ qReject
    decide
  · change p + r - 1 ≤ pairLength n m + Nat.min B 1
    rw [pair_eq]
    omega
  · intro _
    right
    change p + r - 1 + 1 < tapeLength (pairLength n m) B
    unfold tapeLength
    rw [pair_eq]
    omega

private theorem safe_back {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {s p : Nat} (hp : p ≤ n) (hpos : 0 < p) :
    SafeSnapshot s (backConfig B x w p hp) := by
  have hmove : (machine.step (backConfig B x w p hp).state
      ((backConfig B x w p hp).tape (backConfig B x w p hp).head)).2.2 = .left := by
    rw [back_read x w hp hpos]
    rfl
  unfold SafeSnapshot
  rw [hmove]
  refine ⟨?_, ?_, ?_,
    fun i hi => roll_above x w hp (le_refl _) i hi, by simp, ?_⟩
  · change qShiftBack ≠ qAccept
    decide
  · change qShiftBack ≠ qReject
    decide
  · change p + K n m - 1 ≤ pairLength n m + Nat.min B 1
    rw [pair_eq]
    omega
  · intro _
    right
    change 0 < p + K n m - 1
    unfold K
    omega

private theorem safe_origin {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {s : Nat} : SafeSnapshot s (originClassConfig B x w) := by
  have hmove : (machine.step (originClassConfig B x w).state
      ((originClassConfig B x w).tape (originClassConfig B x w).head)).2.2 = .left := by
    rw [origin_read x w]
    exact congrArg (fun a => a.2.2) (class_none _)
  unfold SafeSnapshot
  rw [hmove]
  refine ⟨?_, ?_, ?_,
    fun i hi => clear_above x w (by omega) i hi, by simp, ?_⟩
  · change classState _ ≠ qAccept
    cases h : blockCell x w 0 1 with
    | none => simp [classState]; decide
    | some b => cases b <;> simp [classState] <;> decide
  · change classState _ ≠ qReject
    cases h : blockCell x w 0 1 with
    | none => simp [classState]; decide
    | some b => cases b <;> simp [classState] <;> decide
  · change 1 ≤ pairLength n m + Nat.min B 1
    unfold pairLength
    omega
  · intro _
    right
    change 0 < 1
    omega

private theorem safe_source {n m B : Nat} (x : Bitstring n) (w : Bitstring m) :
    SafeSnapshot 0 (sourceConfig B x w) := by
  have hmove : (machine.step (sourceConfig B x w).state
      ((sourceConfig B x w).tape (sourceConfig B x w).head)).2.2 = .left := by
    rw [source_read x w]
    rfl
  unfold SafeSnapshot
  rw [hmove]
  refine ⟨?_, ?_, ?_, fun i hi => block_above x w (by omega) i hi,
    by simp, ?_⟩
  · change qStart ≠ qAccept
    decide
  · change qStart ≠ qReject
    decide
  · cases B <;> simp [sourceConfig, sourceHead]
  · intro _
    right
    cases B <;> simp [sourceConfig, sourceHead]
    all_goals unfold pairLength
    all_goals omega

private theorem safe_norm {n m B : Nat} (x : Bitstring n) (w : Bitstring m) :
    SafeSnapshot 1 (normConfig B x w) := by
  cases B with
  | zero =>
      have hmove : (machine.step (normConfig 0 x w).state
          ((normConfig 0 x w).tape (normConfig 0 x w).head)).2.2 = .right := by
        rw [norm_read x w]
        rfl
      unfold SafeSnapshot
      rw [hmove]
      refine ⟨?_, ?_, ?_,
        fun i hi => block_above x w (by omega) i hi, ?_, by simp⟩
      · change qNormalize ≠ qAccept
        decide
      · change qNormalize ≠ qReject
        decide
      · change pairLength n m + Nat.min 0 1 - 1 ≤ pairLength n m + Nat.min 0 1
        omega
      · intro _
        right
        change pairLength n m + Nat.min 0 1 - 1 + 1 <
          tapeLength (pairLength n m) 0
        simp only [Nat.zero_min, Nat.add_zero]
        unfold tapeLength pairLength
        omega
  | succ B =>
      have hmove : (machine.step (normConfig (B + 1) x w).state
          ((normConfig (B + 1) x w).tape
            (normConfig (B + 1) x w).head)).2.2 = .left := by
        rw [norm_read x w]
        rfl
      unfold SafeSnapshot
      rw [hmove]
      refine ⟨?_, ?_, ?_,
        fun i hi => block_above x w (by omega) i hi, by simp, ?_⟩
      · change qNormalize ≠ qAccept
        decide
      · change qNormalize ≠ qReject
        decide
      · change pairLength n m + Nat.min (B + 1) 1 - 1 ≤
          pairLength n m + Nat.min (B + 1) 1
        omega
      · intro _
        right
        change 0 < pairLength n m + Nat.min (B + 1) 1 - 1
        simp only [Nat.min_eq_right (by omega : 1 ≤ B + 1)]
        unfold pairLength
        omega

private theorem safe_entry {n m B : Nat} (x : Bitstring n) (w : Bitstring m) :
    SafeSnapshot 2 (entryConfig B x w) := by
  have hmove : (machine.step (entryConfig B x w).state
      ((entryConfig B x w).tape (entryConfig B x w).head)).2.2 = .right := by
    exact congrArg (fun a => a.2.2) (checkAt_action _)
  unfold SafeSnapshot
  rw [hmove]
  refine ⟨?_, ?_, ?_, fun i hi => block_above x w (by omega) i hi,
    ?_, by simp⟩
  · change qCheckAt ≠ qAccept
    decide
  · change qCheckAt ≠ qReject
    decide
  · change (if B = 0 then pairLength n m else pairLength n m - 1) ≤
      pairLength n m + Nat.min B 1
    split <;> omega
  · intro _
    cases B with
    | zero =>
        left
        refine ⟨rfl, rfl, ?_⟩
        change pairLength n m = pairLength n m
        rfl
    | succ B =>
        right
        change (if B + 1 = 0 then pairLength n m else pairLength n m - 1) + 1 <
          tapeLength (pairLength n m) (B + 1)
        unfold tapeLength
        simp
        unfold pairLength
        omega

private theorem trace_safe {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    (s : Nat) (hs : s < clock n m) :
    SafeSnapshot s (machine.run s (startConfig B x w)) := by
  by_cases hsmall : s < 3
  · have hcases : s = 0 ∨ s = 1 ∨ s = 2 := by omega
    rcases hcases with rfl | rfl | rfl
    · rw [start_source x w]
      exact safe_source x w
    · simp only [UniformTM.run]
      rw [start_source x w, step_source x w]
      exact safe_norm x w
    · simp only [UniformTM.run]
      rw [start_source x w, step_source x w, step_norm x w]
      exact safe_entry x w
  · obtain ⟨k, d, hdR, he⟩ := phaseStart_decompose n m s (by omega)
    have hk : k ≤ n := phase_index_le (Nat.le_of_lt hs) he
    have hrun : machine.run s (startConfig B x w) =
        machine.run d
          (saveConfig B x w (n - k) 0 (by omega) (by unfold K; omega)) := by
      rw [he, machine.run_add, run_save x w k hk]
    rcases Nat.lt_or_eq_of_le hk with hkn | hkeq
    · have hp : 0 < n - k := by omega
      by_cases hscan : d < 7 * K n m
      · obtain ⟨j, e, he6, hde⟩ := mod_seven d
        have hj : j < K n m := by omega
        have ph := run_scan_phases (B := B) x w (p := n - k) (j := j)
          (hp := by omega) (hj := hj) (hstop := Or.inl hp) (hcell := by omega)
        dsimp at ph
        have hec : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 5 ∨ e = 6 := by omega
        rcases hec with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · rw [hrun, hde, Nat.add_zero, ph.1]
          exact safe_save x w (by omega) hj
        · rw [hrun, hde, ph.2.1]
          exact safe_try x w (by omega) hj (by omega)
        · rw [hrun, hde, ph.2.2.1]
          exact safe_bounce x w (by omega) hj
        · rw [hrun, hde, ph.2.2.2.1]
          exact safe_class x w (by omega) hj
        · rw [hrun, hde, ph.2.2.2.2.1]
          exact safe_restore x w (by omega) hj
        · rw [hrun, hde, ph.2.2.2.2.2.1]
          exact safe_left x w (by omega) hj (by omega)
        · rw [hrun, hde, ph.2.2.2.2.2.2]
          exact safe_check x w (by omega) (by omega) (by omega)
      · let z := d - 7 * K n m
        have hdz : d = 7 * K n m + z := by dsimp [z]; omega
        have hz : z < 3 * K n m + 3 := by unfold R at hdR; omega
        obtain ⟨r, e, he2, hze⟩ := mod_three_local z
        have hr : r ≤ K n m := by omega
        rcases Nat.lt_or_eq_of_le hr with hrK | rfl
        · have ph := run_shift_phases (B := B) x w (p := n - k) (r := r)
            (hp := by omega) (hpos := hp) (hr := hrK)
          dsimp at ph
          have hec : e = 0 ∨ e = 1 ∨ e = 2 := by omega
          rcases hec with rfl | rfl | rfl
          · rw [hrun, hdz, hze, Nat.add_zero, ph.1]
            exact safe_take x w (by omega) hp (by omega)
          · rw [hrun, hdz, hze,
              show 7 * K n m + (3 * r + 1) = 7 * K n m + 3 * r + 1 by omega,
              ph.2.1]
            exact safe_put x w (by omega) hp hrK
          · rw [hrun, hdz, hze,
              show 7 * K n m + (3 * r + 2) = 7 * K n m + 3 * r + 2 by omega,
              ph.2.2]
            exact safe_gap x w (by omega) hp (by omega) (by omega)
        · have hec : e = 0 ∨ e = 1 ∨ e = 2 := by omega
          have tail := run_shift_tail (B := B) x w (p := n - k)
            (hp := by omega) (hpos := hp)
          dsimp at tail
          rcases hec with rfl | rfl | rfl
          · have htake := run_take_shift (B := B) x w (p := n - k)
              (r := K n m) (hp := by omega) (hpos := hp) (hr := le_refl _)
            rw [hrun, hdz, hze, Nat.add_zero, htake]
            exact safe_take x w (by omega) hp (le_refl _)
          · rw [hrun, hdz, hze,
              show 7 * K n m + (3 * K n m + 1) = 10 * K n m + 1 by ring,
              tail.1]
            exact safe_back x w (by omega) hp
          · rw [hrun, hdz, hze,
              show 7 * K n m + (3 * K n m + 2) = 10 * K n m + 2 by ring,
              tail.2]
            exact safe_check x w (hp := by omega) (hj := by omega)
              (hlast := by intro h; unfold K at h; omega)
    · subst k
      have hrun0 : machine.run s (startConfig B x w) =
          machine.run d
            (saveConfig B x w 0 0 (by omega) (by unfold K; omega)) := by
        simpa only [Nat.sub_self] using hrun
      have hdF : d < 7 * (K n m - 1) + 4 := by
        have hc := clock_phase n m
        omega
      by_cases hnormal : d < 7 * (K n m - 1)
      · obtain ⟨j, e, he6, hde⟩ := mod_seven d
        have hj : j < K n m - 1 := by omega
        have ph := run_final_scan_phases (B := B) x w hj
        dsimp at ph
        have hec : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 5 ∨ e = 6 := by omega
        rcases hec with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · rw [hrun0, hde, Nat.add_zero, ph.1]
          exact safe_save x w (by omega) (by omega)
        · rw [hrun0, hde, ph.2.1]
          exact safe_try x w (by omega) (by omega) (by omega)
        · rw [hrun0, hde, ph.2.2.1]
          exact safe_bounce x w (by omega) (by omega)
        · rw [hrun0, hde, ph.2.2.2.1]
          exact safe_class x w (by omega) (by omega)
        · rw [hrun0, hde, ph.2.2.2.2.1]
          exact safe_restore x w (by omega) (by omega)
        · rw [hrun0, hde, ph.2.2.2.2.2.1]
          exact safe_left x w (by omega) (by omega) (by omega)
        · rw [hrun0, hde, ph.2.2.2.2.2.2]
          exact safe_check x w (by omega) (by omega) (by omega)
      · have hz : d = 7 * (K n m - 1) ∨
            d = 7 * (K n m - 1) + 1 ∨
            d = 7 * (K n m - 1) + 2 ∨
            d = 7 * (K n m - 1) + 3 := by omega
        have tail := run_final_tail (B := B) x w
        dsimp at tail
        rcases hz with rfl | rfl | rfl | rfl
        · rw [hrun0, tail.1]
          exact safe_save x w (by omega) (by unfold K; omega)
        · rw [hrun0, tail.2.1]
          exact safe_try x w (by omega) (by unfold K; omega) (by
            intro _
            have hc := clock_phase n m
            omega)
        · rw [hrun0, tail.2.2.1]
          exact safe_bounce x w (by omega) (by unfold K; omega)
        · rw [hrun0, tail.2.2.2.1]
          exact safe_origin x w

private theorem run_entry_two {n m B : Nat} (x : Bitstring n) (w : Bitstring m) :
    machine.run 2 (startConfig B x w) = entryConfig B x w := by
  simp only [UniformTM.run]
  rw [start_source x w, step_source x w, step_norm x w]

private theorem run_last_try {n m B : Nat} (x : Bitstring n) (w : Bitstring m) :
    machine.run (clock n m - 3) (startConfig B x w) =
      tryConfig B x w 0 (K n m - 1) (by omega) (by unfold K; omega) := by
  have htail := (run_final_tail (B := B) x w).2.1
  have hc := clock_phase n m
  have hs0 : machine.run (phaseStart n m n) (startConfig B x w) =
      saveConfig B x w 0 0 (by omega) (by unfold K; omega) := by
    simpa only [Nat.sub_self] using run_save (B := B) x w n (le_refl _)
  rw [show clock n m - 3 = phaseStart n m n +
      (7 * (K n m - 1) + 1) by omega, machine.run_add, hs0]
  exact htail

/-- Literal accepting fields and the complete `[x][w][marker][blanks]`
layout.  The marker clause records only its literal value; it makes no claim
that this phase recognizes marker values. -/
theorem final_fields_and_layout {n m B : Nat} (x : Bitstring n) (w : Bitstring m) :
    let c := machine.run (clock n m) (startConfig B x w)
    c = finalConfig B x w ∧ c.state = qAccept ∧ c.state = machine.accept ∧
    c.head = (⟨0, by unfold tapeLength; omega⟩ :
      Fin (tapeLength (pairLength n m) B)) ∧ c.head.val = 0 ∧
    c.tape = alignedTape B x w ∧
    (∀ j : Fin n, c.tape
      ⟨j.val, by unfold tapeLength pairLength; omega⟩ = some (x j)) ∧
    (∀ j : Fin m, c.tape
      ⟨n + j.val, by unfold tapeLength pairLength; omega⟩ = some (w j)) ∧
    c.tape ⟨n + m, by unfold tapeLength pairLength; omega⟩ = some true ∧
    (∀ i : Fin (tapeLength (pairLength n m) B),
      n + m + 1 ≤ i.val → c.tape i = none) := by
  dsimp
  rw [run_exact]
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro j
    exact block_read x w (p := 0) (k := j.val)
      (by omega) (by unfold K; omega) _ rfl |>.trans
      (congrArg some (bit_x x w j))
  · intro j
    exact block_read x w (p := 0) (k := n + j.val)
      (by omega) (by unfold K; omega) _ rfl |>.trans
      (congrArg some (bit_w x w j))
  · exact block_read x w (p := 0) (k := n + m)
      (by omega) (by unfold K; omega) _ rfl |>.trans
      (congrArg some (bit_marker x w))
  · intro i hi
    exact block_blank x w (Or.inr (by unfold K; omega)) i rfl

/-- The accepting control is the strict first terminal control. -/
theorem strict_first_terminal {n m B : Nat} (x : Bitstring n) (w : Bitstring m) :
    (∀ s, s < clock n m →
      (machine.run s (startConfig B x w)).state ≠ qAccept ∧
      (machine.run s (startConfig B x w)).state ≠ qReject) ∧
    (machine.run (clock n m) (startConfig B x w)).state = qAccept := by
  refine ⟨?_, (final_fields_and_layout x w).2.1⟩
  intro s hs
  exact ⟨(trace_safe x w s hs).1, (trace_safe x w s hs).2.1⟩

/-- Acceptance is absorbing, with the exact literal final configuration at
every post-clock time. -/
theorem accepting_absorption {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    (extra : Nat) :
    machine.run (clock n m + extra) (startConfig B x w) = finalConfig B x w ∧
    (machine.run (clock n m + extra) (startConfig B x w)).state = qAccept ∧
    (machine.run (clock n m + extra) (startConfig B x w)).head.val = 0 ∧
    (machine.run (clock n m + extra) (startConfig B x w)).tape =
      alignedTape B x w := by
  have hrun : machine.run (clock n m + extra) (startConfig B x w) =
      finalConfig B x w := by
    rw [machine.run_add, run_exact,
      machine.run_accept (finalConfig B x w) rfl extra]
  rw [hrun]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Exact head/write footprint through the clock.  Since each step writes its
scanned address, the third clause bounds every source write address; time zero
attains the bound.  All allocated cells above the input extent stay blank. -/
theorem footprint_through_clock {n m B : Nat} (x : Bitstring n) (w : Bitstring m) :
    (∀ s, s ≤ clock n m →
      (machine.run s (startConfig B x w)).head.val ≤
        pairLength n m + Nat.min B 1) ∧
    (machine.run 0 (startConfig B x w)).head.val =
      pairLength n m + Nat.min B 1 ∧
    (∀ s, s < clock n m →
      (machine.run s (startConfig B x w)).head.val ≤
        pairLength n m + Nat.min B 1) ∧
    (∀ s, s ≤ clock n m → ∀ i : Fin (tapeLength (pairLength n m) B),
      pairLength n m ≤ i.val →
      (machine.run s (startConfig B x w)).tape i = none) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs
    rcases Nat.lt_or_eq_of_le hs with hlt | rfl
    · exact (trace_safe x w s hlt).2.2.1
    · rw [run_exact]
      change 0 ≤ pairLength n m + Nat.min B 1
      omega
  · simp only [UniformTM.run]
    rw [start_source x w]
    cases B <;> simp [sourceConfig, sourceHead]
  · exact fun s hs => (trace_safe x w s hs).2.2.1
  · intro s hs i hi
    rcases Nat.lt_or_eq_of_le hs with hlt | rfl
    · exact (trace_safe x w s hlt).2.2.2.1 i hi
    · rw [run_exact]
      exact block_blank x w (p := 0) (k := i.val) (Or.inr (by
        have he := pair_eq n m
        omega)) i rfl

/-- Complete clamp characterization.  The sole right clamp is the zero-budget
entry transition at source time two.  The sole left clamp, for every budget,
is the final origin probe at source time `clock - 3`. -/
theorem boundary_clamps {n m B : Nat} (x : Bitstring n) (w : Bitstring m) :
    (∀ s, s < clock n m →
      let c := machine.run s (startConfig B x w)
      ((machine.step c.state (c.tape c.head)).2.2 = .right ∧
        moveHead c.head .right = c.head ↔ s = 2 ∧ B = 0)) ∧
    (∀ s, s < clock n m →
      let c := machine.run s (startConfig B x w)
      ((machine.step c.state (c.tape c.head)).2.2 = .left ∧
        moveHead c.head .left = c.head ↔ s = clock n m - 3)) ∧
    ((let c := machine.run 2 (startConfig B x w);
      c.head.val = (if B = 0 then pairLength n m else pairLength n m - 1) ∧
      (machine.step c.state (c.tape c.head)).2.2 = .right) ∧
    (let c := machine.run (clock n m - 3) (startConfig B x w);
      c.head.val = 0 ∧
      (machine.step c.state (c.tape c.head)).2.2 = .left)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs
    dsimp
    constructor
    · rintro ⟨hm, hclamp⟩
      rcases (trace_safe x w s hs).2.2.2.2.1 hm with hspecial | hinterior
      · exact ⟨hspecial.1, hspecial.2.1⟩
      · have hv := congrArg Fin.val hclamp
        rw [move_right_val _ hinterior] at hv
        omega
    · rintro ⟨rfl, rfl⟩
      rw [run_entry_two x w]
      refine ⟨?_, ?_⟩
      · exact congrArg (fun a => a.2.2) (checkAt_action _)
      · apply Fin.ext
        change (moveHead (cell 0 (pairLength n m) (by omega)) .right).val =
          (cell 0 (pairLength n m) (by omega)).val
        unfold moveHead cell tapeLength
        simp
  · intro s hs
    dsimp
    constructor
    · rintro ⟨hm, hclamp⟩
      rcases (trace_safe x w s hs).2.2.2.2.2 hm with hspecial | hpos
      · exact hspecial.1
      · have hv := congrArg Fin.val hclamp
        change (machine.run s (startConfig B x w)).head.val - 1 =
          (machine.run s (startConfig B x w)).head.val at hv
        omega
    · intro he
      subst s
      rw [run_last_try x w]
      refine ⟨?_, ?_⟩
      · rw [try_read x w (by omega) (by unfold K; omega)]
        exact congrArg (fun a => a.2.2) (try_action _ _)
      · apply Fin.ext
        change (0 + K n m - 1 - (K n m - 1)) - 1 =
          0 + K n m - 1 - (K n m - 1)
        unfold K
        omega
  · rw [run_entry_two x w]
    refine ⟨?_, ?_⟩
    · change (if B = 0 then pairLength n m else pairLength n m - 1) =
        (if B = 0 then pairLength n m else pairLength n m - 1)
      rfl
    · exact congrArg (fun a => a.2.2) (checkAt_action _)
  · rw [run_last_try x w]
    refine ⟨?_, ?_⟩
    · change 0 + K n m - 1 - (K n m - 1) = 0
      unfold K
      omega
    rw [try_read x w (by omega) (by unfold K; omega)]
    exact congrArg (fun a => a.2.2) (try_action _ _)
