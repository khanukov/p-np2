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
