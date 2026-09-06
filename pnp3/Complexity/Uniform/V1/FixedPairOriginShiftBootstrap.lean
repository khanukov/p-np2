import Complexity.Uniform.V1.FixedPairTagRemoval
/-! Seven-state structural one-cell left shift. Recovery is fixed-extent only: for `n > 0` cell zero stays blank, so this is not full origin alignment; no cross-split reconstruction is claimed. -/
namespace Pnp3.Complexity.Uniform.V1
namespace FixedPairOriginShiftBootstrap
open PairEncoding
abbrev shiftStateCount : Nat := 7
def qStart : Fin shiftStateCount := ⟨0, by decide⟩
private def qCarryF : Fin shiftStateCount := ⟨1, by decide⟩
private def qCarryT : Fin shiftStateCount := ⟨2, by decide⟩
private def qHole : Fin shiftStateCount := ⟨3, by decide⟩
private def qFetch : Fin shiftStateCount := ⟨4, by decide⟩
def qAccept : Fin shiftStateCount := ⟨5, by decide⟩
def qReject : Fin shiftStateCount := ⟨6, by decide⟩
private def raw (q : Fin shiftStateCount) (s : Option Bool) : Fin shiftStateCount × Option Bool × Move :=
  match q.val with
  | 0 => match s with
    | none => (qStart, none, .right)
    | some false => (qCarryF, none, .left)
    | some true => (qCarryT, none, .left)
  | 1 => match s with
    | none => (qHole, some false, .right)
    | some b => (qReject, some b, .stay)
  | 2 => match s with
    | none => (qHole, some true, .right)
    | some b => (qReject, some b, .stay)
  | 3 => match s with
    | none => (qFetch, none, .right)
    | some b => (qReject, some b, .stay)
  | 4 => match s with
    | none => (qAccept, none, .stay)
    | some false => (qCarryF, none, .left)
    | some true => (qCarryT, none, .left)
  | 5 => (qAccept, s, .stay)
  | _ => (qReject, s, .stay)
def machine : UniformTM where
  stateCount := shiftStateCount
  start := qStart
  accept := qAccept
  reject := qReject
  accept_ne_reject := by decide
  rawStep := raw
theorem raw_table : (∀ s, machine.rawStep qStart s = match s with
      | none => (qStart, none, .right)
      | some false => (⟨1, by decide⟩, none, .left)
      | some true => (⟨2, by decide⟩, none, .left)) ∧
    (∀ s, machine.rawStep ⟨1, by decide⟩ s = match s with
      | none => (⟨3, by decide⟩, some false, .right)
      | some b => (qReject, some b, .stay)) ∧
    (∀ s, machine.rawStep ⟨2, by decide⟩ s = match s with
      | none => (⟨3, by decide⟩, some true, .right)
      | some b => (qReject, some b, .stay)) ∧
    (∀ s, machine.rawStep ⟨3, by decide⟩ s = match s with
      | none => (⟨4, by decide⟩, none, .right)
      | some b => (qReject, some b, .stay)) ∧
    (∀ s, machine.rawStep ⟨4, by decide⟩ s = match s with
      | none => (qAccept, none, .stay)
      | some false => (⟨1, by decide⟩, none, .left)
      | some true => (⟨2, by decide⟩, none, .left)) ∧
    (∀ s, machine.rawStep qAccept s = (qAccept, s, .stay)) ∧
    (∀ s, machine.rawStep qReject s = (qReject, s, .stay)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro s <;> rfl
theorem resource_pins : machine.stateCount = 7 ∧ machine.start = qStart ∧
    machine.accept = qAccept ∧ machine.reject = qReject ∧
    qStart.val = 0 ∧ qAccept.val = 5 ∧ qReject.val = 6 ∧
    Fintype.card (Fin machine.stateCount × Option Bool) = 21 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  change Fintype.card (Fin 7 × Option Bool) = 21
  decide
def retag {N B : Nat} (c : Config FixedPairTagRemoval.removalStateCount N B) : Config shiftStateCount N B where
  state := qStart
  head := c.head
  tape := c.tape
def startConfig {n m : Nat} (B : Nat) (x : Bitstring n) (w : Bitstring m) : Config shiftStateCount (pairLength n m) B :=
  retag (FixedPairTagRemoval.finalConfig B x w)
theorem handoff_exact {n m B : Nat} (x : Bitstring n) (w : Bitstring m) :
    let p := FixedPairTagRemoval.machine.run (FixedPairTagRemoval.clock n)
      (FixedPairTagRemoval.startConfig B x w)
    p = FixedPairTagRemoval.finalConfig B x w ∧
    p.state = FixedPairTagRemoval.qAccept ∧
    (startConfig B x w).state = qStart ∧
    (startConfig B x w).head = p.head ∧
    (startConfig B x w).tape = p.tape := by
  dsimp
  rw [FixedPairTagRemoval.run_encoded_exact]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩
def clock (n m : Nat) : Nat := 4 * n + 3 * m + 5
theorem clock_exact (n m : Nat) : clock n m = (n + 1) + 3 * (n + m + 1) + 1 ∧
    clock 0 0 = 5 ∧ clock n m ≤ 4 * (n + m + 1) + 1 := by
  unfold clock
  omega
private def K (n m : Nat) : Nat := n + m + 1
private theorem K_pos (n m : Nat) : 0 < K n m := by unfold K; omega
private theorem pair_eq (n m : Nat) : pairLength n m = n + K n m := by unfold pairLength K; omega
private def bit {n m : Nat} (x : Bitstring n) (w : Bitstring m) (r : Nat) : Bool :=
  if h : r < n + m then Fin.append x w ⟨r, h⟩ else true
private theorem bit_append {n m : Nat} (x : Bitstring n) (w : Bitstring m) (j : Fin (n + m)) : bit x w j.val = Fin.append x w j := by
  unfold bit
  rw [dif_pos j.isLt]
private theorem bit_x {n m : Nat} (x : Bitstring n) (w : Bitstring m) (j : Fin n) : bit x w j.val = x j := by
  exact (bit_append x w (Fin.castAdd m j)).trans (Fin.append_left x w j)
private theorem bit_w {n m : Nat} (x : Bitstring n) (w : Bitstring m) (j : Fin m) : bit x w (n + j.val) = w j := by
  exact (bit_append x w (Fin.natAdd n j)).trans (Fin.append_right x w j)
private theorem bit_marker {n m : Nat} (x : Bitstring n) (w : Bitstring m) : bit x w (n + m) = true := by simp [bit]
private def sourceCell {n m : Nat} (x : Bitstring n) (w : Bitstring m)
    (k : Nat) : Option Bool :=
  if k ≤ n then none
  else if k ≤ pairLength n m then some (bit x w (k - n - 1))
  else none
private def finalCell {n m : Nat} (x : Bitstring n) (w : Bitstring m)
    (k : Nat) : Option Bool :=
  if n ≤ k ∧ k < pairLength n m then some (bit x w (k - n)) else none
def shiftedTape {n m : Nat} (B : Nat) (x : Bitstring n) (w : Bitstring m) : Fin (tapeLength (pairLength n m) B) → Option Bool :=
  fun i => finalCell x w i.val
private def finalHead (n m B : Nat) : Fin (tapeLength (pairLength n m) B) :=
  if h : B = 0 then
    ⟨pairLength n m, by unfold tapeLength; omega⟩
  else
    ⟨pairLength n m + 1, by
      have hb : 1 ≤ B := Nat.one_le_iff_ne_zero.mpr h
      unfold tapeLength
      omega⟩
private theorem finalHead_val (n m B : Nat) : (finalHead n m B).val = if B = 0 then pairLength n m else pairLength n m + 1 := by
  cases B <;> rfl
private theorem finalHead_min (n m B : Nat) : (finalHead n m B).val = pairLength n m + Nat.min B 1 := by
  cases B <;> simp [finalHead]
private theorem finalHead_ge (n m B : Nat) : pairLength n m ≤ (finalHead n m B).val := by
  rw [finalHead_val]
  split <;> omega
private theorem finalHead_le (n m B : Nat) : (finalHead n m B).val ≤ pairLength n m + 1 := by
  rw [finalHead_val]
  split <;> omega
private theorem finalHead_scope {n m B B' : Nat} (h : B = 0 ↔ B' = 0) : (finalHead n m B).val = (finalHead n m B').val := by
  rw [finalHead_val n m B, finalHead_val n m B']
  by_cases hB : B = 0
  · rw [if_pos hB, if_pos (h.mp hB)]
  · have hB' : B' ≠ 0 := fun hb => hB (h.mpr hb)
    rw [if_neg hB, if_neg hB']
def finalConfig {n m : Nat} (B : Nat) (x : Bitstring n) (w : Bitstring m) : Config shiftStateCount (pairLength n m) B where
  state := qAccept
  head := finalHead n m B
  tape := shiftedTape B x w
private theorem compact_left {n m B : Nat} (x : Bitstring n) (w : Bitstring m) (i : Fin (tapeLength (pairLength n m) B)) (hi : i.val ≤ n) : FixedPairTagRemoval.compactTape B x w i = none := by
  unfold FixedPairTagRemoval.compactTape
  rw [dif_pos hi]
private theorem compact_right {n m B : Nat} (x : Bitstring n) (w : Bitstring m) (i : Fin (tapeLength (pairLength n m) B)) (hi : pairLength n m < i.val) : FixedPairTagRemoval.compactTape B x w i = none := by
  have hp : pairLength n m = 2 * n + 1 + m := by unfold pairLength; omega
  unfold FixedPairTagRemoval.compactTape
  rw [dif_neg (by omega), dif_neg (by omega)]
  unfold FixedPairConcatSentinel.sentinelTape
  rw [dif_neg (by omega), if_neg (by omega)]
private theorem compact_block {n m B : Nat} (x : Bitstring n) (w : Bitstring m) (r : Nat) (hr : r < K n m) (i : Fin (tapeLength (pairLength n m) B)) (hi : i.val = n + 1 + r) : FixedPairTagRemoval.compactTape B x w i = some (bit x w r) := by
  by_cases hc : r < n + m
  · have h := FixedPairTagRemoval.final_content_contiguous (B := B) x w
      (⟨r, hc⟩ : Fin (n + m))
    rw [FixedPairTagRemoval.run_encoded_exact] at h
    change FixedPairTagRemoval.compactTape B x w
      ⟨n + 1 + r, by unfold tapeLength pairLength; omega⟩ =
        some (Fin.append x w ⟨r, hc⟩) at h
    let j : Fin (tapeLength (pairLength n m) B) :=
      ⟨n + 1 + r, by unfold tapeLength pairLength; omega⟩
    have hij : i = j := Fin.ext hi
    calc
      FixedPairTagRemoval.compactTape B x w i =
          FixedPairTagRemoval.compactTape B x w j := congrArg _ hij
      _ = some (Fin.append x w ⟨r, hc⟩) := h
      _ = some (bit x w r) := congrArg some (bit_append x w ⟨r, hc⟩).symm
  · have hre : r = n + m := by unfold K at hr; omega
    have hp := pair_eq n m
    unfold K at hp
    have h := (FixedPairTagRemoval.final_tape_behavior (B := B) x w).2.2.2.1
    rw [FixedPairTagRemoval.run_encoded_exact] at h
    change FixedPairTagRemoval.compactTape B x w
      ⟨pairLength n m, by unfold tapeLength; omega⟩ = some true at h
    let j : Fin (tapeLength (pairLength n m) B) :=
      ⟨pairLength n m, by unfold tapeLength; omega⟩
    have hv : i.val = pairLength n m := by
      unfold pairLength at *
      omega
    have hij : i = j := Fin.ext hv
    calc
      FixedPairTagRemoval.compactTape B x w i =
          FixedPairTagRemoval.compactTape B x w j := congrArg _ hij
      _ = some true := h
      _ = some (bit x w r) := by rw [hre, bit_marker]
private theorem compact_read {n m B : Nat} (x : Bitstring n) (w : Bitstring m) (i : Fin (tapeLength (pairLength n m) B)) : FixedPairTagRemoval.compactTape B x w i = sourceCell x w i.val := by
  unfold sourceCell
  by_cases hl : i.val ≤ n
  · rw [if_pos hl]
    exact compact_left x w i hl
  · rw [if_neg hl]
    by_cases hp : i.val ≤ pairLength n m
    · rw [if_pos hp]
      have hpair := pair_eq n m
      have hr : i.val - n - 1 < K n m := by omega
      exact compact_block x w (i.val - n - 1) hr i (by omega)
    · rw [if_neg hp]
      exact compact_right x w i (by omega)
private def rollCell {n m : Nat} (x : Bitstring n) (w : Bitstring m)
    (r k : Nat) : Option Bool :=
  if k < n then none
  else if k < n + r then some (bit x w (k - n))
  else if k = n + r then none
  else if k ≤ pairLength n m then some (bit x w (k - n - 1))
  else none
private def takeCell {n m : Nat} (x : Bitstring n) (w : Bitstring m)
    (r k : Nat) : Option Bool :=
  if k = n + r + 1 then none else rollCell x w r k
private def rolledTape {n m : Nat} (B : Nat) (x : Bitstring n) (w : Bitstring m) (r : Nat) : Fin (tapeLength (pairLength n m) B) → Option Bool :=
  fun i => rollCell x w r i.val
private def takenTape {n m : Nat} (B : Nat) (x : Bitstring n) (w : Bitstring m) (r : Nat) : Fin (tapeLength (pairLength n m) B) → Option Bool :=
  fun i => takeCell x w r i.val
private theorem roll_zero {n m B : Nat} (x : Bitstring n) (w : Bitstring m) : rolledTape B x w 0 = FixedPairTagRemoval.compactTape B x w := by
  funext i
  rw [compact_read]
  change rollCell x w 0 i.val = sourceCell x w i.val
  unfold sourceCell
  by_cases hl : i.val ≤ n
  · rw [if_pos hl]
    unfold rollCell
    by_cases hlt : i.val < n
    · rw [if_pos hlt]
    · rw [if_neg hlt, if_neg (by omega), if_pos (by omega)]
  · rw [if_neg hl]
    by_cases hp : i.val ≤ pairLength n m
    · rw [if_pos hp]
      unfold rollCell
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos hp]
    · rw [if_neg hp]
      unfold rollCell
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg hp]
private theorem roll_hole {n m : Nat} (x : Bitstring n) (w : Bitstring m) (r : Nat) : rollCell x w r (n + r) = none := by
  unfold rollCell
  rw [if_neg (by omega), if_neg (by omega), if_pos rfl]
private theorem roll_fetch {n m : Nat} (x : Bitstring n) (w : Bitstring m) (r : Nat) (hr : r < K n m) : rollCell x w r (n + 1 + r) = some (bit x w r) := by
  have hp := pair_eq n m
  unfold rollCell
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  rw [show n + 1 + r - n - 1 = r by omega]
private theorem roll_above {n m : Nat} (x : Bitstring n) (w : Bitstring m)
    (r k : Nat) (hr : r ≤ K n m) (hk : pairLength n m < k) :
    rollCell x w r k = none := by
  have hp := pair_eq n m
  unfold rollCell
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
private theorem write_take {n m : Nat} (x : Bitstring n) (w : Bitstring m)
    (r k : Nat) :
    (if k = n + r then some (bit x w r) else takeCell x w r k) =
      rollCell x w (r + 1) k := by
  by_cases h0 : k = n + r
  · rw [if_pos h0]
    unfold rollCell
    rw [if_neg (by omega), if_pos (by omega), show k - n = r by omega]
  · rw [if_neg h0]
    unfold takeCell
    by_cases h1 : k = n + r + 1
    · rw [if_pos h1]
      unfold rollCell
      rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    · rw [if_neg h1]
      by_cases hlo : k < n
      · unfold rollCell
        rw [if_pos hlo, if_pos hlo]
      · by_cases hmid : k < n + r
        · unfold rollCell
          rw [if_neg hlo, if_pos hmid, if_neg hlo, if_pos (by omega)]
        · have hn : ¬k < n := hlo
          have hs : ¬k < n + (r + 1) := by omega
          have he : ¬k = n + (r + 1) := by omega
          unfold rollCell
          rw [if_neg hn, if_neg hmid, if_neg h0, if_neg hn, if_neg hs, if_neg he]
private theorem roll_last {n m B : Nat} (x : Bitstring n) (w : Bitstring m) : rolledTape B x w (K n m) = shiftedTape B x w := by
  funext i
  change rollCell x w (K n m) i.val = finalCell x w i.val
  unfold finalCell
  have hp := pair_eq n m
  by_cases hm : n ≤ i.val ∧ i.val < pairLength n m
  · rw [if_pos hm]
    unfold rollCell
    rw [if_neg (by omega), if_pos (by omega)]
  · rw [if_neg hm]
    by_cases hl : i.val < n
    · unfold rollCell
      rw [if_pos hl]
    · have hpi : pairLength n m ≤ i.val := by omega
      by_cases heq : i.val = pairLength n m
      · unfold rollCell
        rw [if_neg hl, if_neg (by omega), if_pos (by omega)]
      · unfold rollCell
        rw [if_neg hl, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
private theorem rolled_above {n m B : Nat} (x : Bitstring n) (w : Bitstring m) (r : Nat) (hr : r ≤ K n m) (i : Fin (tapeLength (pairLength n m) B)) (hi : pairLength n m < i.val) : rolledTape B x w r i = none :=
  roll_above x w r i.val hr hi
private theorem shifted_above {n m B : Nat} (x : Bitstring n) (w : Bitstring m) (i : Fin (tapeLength (pairLength n m) B)) (hi : pairLength n m ≤ i.val) : shiftedTape B x w i = none := by
  change finalCell x w i.val = none
  unfold finalCell
  rw [if_neg (by omega)]
private theorem erase_eq_taken {n m B : Nat} (x : Bitstring n) (w : Bitstring m) (r : Nat) (h : Fin (tapeLength (pairLength n m) B))
    (hh : h.val = n + 1 + r) :
    (fun i => if i = h then none else rolledTape B x w r i) = takenTape B x w r := by
  funext i
  change (if i = h then none else rollCell x w r i.val) = takeCell x w r i.val
  by_cases hi : i = h
  · have hv := congrArg Fin.val hi
    rw [if_pos hi]
    unfold takeCell
    rw [if_pos (by omega)]
  · rw [if_neg hi]
    have hv : i.val ≠ n + r + 1 := by
      intro he
      apply hi
      apply Fin.ext
      omega
    unfold takeCell
    rw [if_neg hv]
private theorem fill_eq_roll {n m B : Nat} (x : Bitstring n) (w : Bitstring m) (r : Nat) (h : Fin (tapeLength (pairLength n m) B)) (hh : h.val = n + r) : (fun i => if i = h then some (bit x w r) else takenTape B x w r i) =
      rolledTape B x w (r + 1) := by
  funext i
  change (if i = h then some (bit x w r) else takeCell x w r i.val) =
    rollCell x w (r + 1) i.val
  have hu := write_take x w r i.val
  by_cases hi : i = h
  · have hiv := congrArg Fin.val hi
    have hv : i.val = n + r := by omega
    rw [if_pos hi]
    rw [if_pos hv] at hu
    exact hu
  · have hv : i.val ≠ n + r := by
      intro he
      apply hi
      apply Fin.ext
      omega
    rw [if_neg hi]
    rw [if_neg hv] at hu
    exact hu
private def carryState (b : Bool) : Fin shiftStateCount := if b then qCarryT else qCarryF
private def fetchState (r : Nat) : Fin shiftStateCount := if r = 0 then qStart else qFetch
private theorem fetchState_pos {r : Nat} (hr : 0 < r) : fetchState r = qFetch := by
  unfold fetchState
  rw [if_neg (Nat.ne_of_gt hr)]
private def scanHead {n m : Nat} (B j : Nat) : Fin (tapeLength (pairLength n m) B) :=
  if h : j ≤ n + 1 then
    ⟨j, by
      have hp := pair_eq n m
      have hk := K_pos n m
      unfold tapeLength
      omega⟩
  else ⟨0, by unfold tapeLength; omega⟩
private def carryHead {n m : Nat} (B r : Nat) : Fin (tapeLength (pairLength n m) B) :=
  if h : r < K n m then
    ⟨n + r, by
      have hp := pair_eq n m
      unfold tapeLength
      omega⟩
  else ⟨0, by unfold tapeLength; omega⟩
private def holeHead {n m : Nat} (B r : Nat) : Fin (tapeLength (pairLength n m) B) :=
  if h : r ≤ K n m then
    ⟨n + r, by
      have hp := pair_eq n m
      unfold tapeLength
      omega⟩
  else ⟨0, by unfold tapeLength; omega⟩
private def fetchHead {n m : Nat} (B r : Nat) : Fin (tapeLength (pairLength n m) B) :=
  if h : r < K n m then
    ⟨n + 1 + r, by
      have hp := pair_eq n m
      unfold tapeLength
      omega⟩
  else finalHead n m B
private theorem scanHead_val {n m B j : Nat} (hj : j ≤ n + 1) : (scanHead (n := n) (m := m) B j).val = j := by simp only [scanHead, dif_pos hj]
private theorem carryHead_val {n m B r : Nat} (hr : r < K n m) : (carryHead (n := n) (m := m) B r).val = n + r := by simp only [carryHead, dif_pos hr]
private theorem holeHead_val {n m B r : Nat} (hr : r ≤ K n m) : (holeHead (n := n) (m := m) B r).val = n + r := by simp only [holeHead, dif_pos hr]
private theorem fetchHead_lt {n m B r : Nat} (hr : r < K n m) : (fetchHead (n := n) (m := m) B r).val = n + 1 + r := by simp only [fetchHead, dif_pos hr]
private theorem fetchHead_last {n m B : Nat} : (fetchHead (n := n) (m := m) B (K n m)).val = (finalHead n m B).val := by simp only [fetchHead, dif_neg (Nat.lt_irrefl _)]
private def scanConfig {n m : Nat} (B : Nat) (x : Bitstring n) (w : Bitstring m) (j : Nat) : Config shiftStateCount (pairLength n m) B where
  state := qStart
  head := scanHead B j
  tape := FixedPairTagRemoval.compactTape B x w
private def fetchConfig {n m : Nat} (B : Nat) (x : Bitstring n) (w : Bitstring m) (r : Nat) : Config shiftStateCount (pairLength n m) B where
  state := fetchState r
  head := fetchHead B r
  tape := rolledTape B x w r
private def carryConfig {n m : Nat} (B : Nat) (x : Bitstring n) (w : Bitstring m) (r : Nat) : Config shiftStateCount (pairLength n m) B where
  state := carryState (bit x w r)
  head := carryHead B r
  tape := takenTape B x w r
private def holeConfig {n m : Nat} (B : Nat) (x : Bitstring n) (w : Bitstring m) (r : Nat) : Config shiftStateCount (pairLength n m) B where
  state := qHole
  head := holeHead B r
  tape := rolledTape B x w r
private theorem scanConfig_head_val {n m B j : Nat} {x : Bitstring n} {w : Bitstring m} (hj : j ≤ n + 1) :
    (scanConfig B x w j).head.val = j := scanHead_val hj
private theorem carryConfig_head_val {n m B r : Nat} {x : Bitstring n} {w : Bitstring m} (hr : r < K n m) :
    (carryConfig B x w r).head.val = n + r := carryHead_val hr
private theorem holeConfig_head_val {n m B r : Nat} {x : Bitstring n} {w : Bitstring m} (hr : r ≤ K n m) :
    (holeConfig B x w r).head.val = n + r := holeHead_val hr
private theorem fetchConfig_head_lt {n m B r : Nat} {x : Bitstring n} {w : Bitstring m} (hr : r < K n m) :
    (fetchConfig B x w r).head.val = n + 1 + r := fetchHead_lt hr
private theorem fetchConfig_head_last {n m B : Nat} {x : Bitstring n} {w : Bitstring m} :
    (fetchConfig B x w (K n m)).head.val = (finalHead n m B).val := fetchHead_last
private theorem config_ext {N B : Nat} {c d : Config shiftStateCount N B} (hs : c.state = d.state) (hh : c.head = d.head) (ht : c.tape = d.tape) : c = d := by
  cases c with
  | mk cs ch ct =>
      cases d with
      | mk ds dh dt =>
          change cs = ds at hs
          change ch = dh at hh
          change ct = dt at ht
          subst ds
          subst dh
          subst dt
          rfl
private theorem stepConfig_eq {N B : Nat} (c : Config shiftStateCount N B)
    (q : Fin shiftStateCount) (s : Option Bool) (mv : Move)
    (ha : machine.step c.state (c.tape c.head) = (q, s, mv)) :
    machine.stepConfig c =
      ({ state := q, head := moveHead c.head mv,
         tape := fun i => if i = c.head then s else c.tape i } :
        Config shiftStateCount N B) := by
  apply config_ext
  · change (machine.step c.state (c.tape c.head)).1 = q
    rw [ha]
  · change moveHead c.head (machine.step c.state (c.tape c.head)).2.2 = _
    rw [ha]
  · funext i
    change (if i = c.head then (machine.step c.state (c.tape c.head)).2.1
      else c.tape i) = (if i = c.head then s else c.tape i)
    rw [ha]
private theorem move_right_val {L : Nat} (h : Fin L) (hb : h.val + 1 < L) : (moveHead h .right).val = h.val + 1 := by
  unfold moveHead
  rw [dif_pos hb]
private theorem update_same {L : Nat} {α : Type} (t : Fin L → α) (h : Fin L) (s : α) (hs : t h = s) : (fun i => if i = h then s else t i) = t := by
  funext i
  by_cases hi : i = h
  · rw [if_pos hi, hi]
    exact hs.symm
  · rw [if_neg hi]
private theorem fetch_some (r : Nat) (b : Bool) : machine.step (fetchState r) (some b) = (carryState b, none, .left) := by
  cases r <;> cases b <;> rfl
private theorem carry_none (b : Bool) : machine.step (carryState b) none = (qHole, some b, .right) := by
  cases b <;> rfl
private theorem hole_none : machine.step qHole none = (qFetch, none, .right) := by rfl
private theorem fetch_none {r : Nat} (hr : 0 < r) : machine.step (fetchState r) none = (qAccept, none, .stay) := by
  rw [fetchState_pos hr]
  rfl
private theorem scan_read {n m B : Nat} (x : Bitstring n) (w : Bitstring m) (j : Nat) (hj : j < n + 1) : (scanConfig B x w j).tape (scanConfig B x w j).head = none := by
  calc
    (scanConfig B x w j).tape (scanConfig B x w j).head =
        sourceCell x w (scanConfig B x w j).head.val := compact_read x w _
    _ = sourceCell x w j := congrArg (sourceCell x w) (scanHead_val (by omega))
    _ = none := by unfold sourceCell; rw [if_pos (by omega)]
private theorem scan_block_read {n m B : Nat} (x : Bitstring n) (w : Bitstring m) : (scanConfig B x w (n + 1)).tape (scanConfig B x w (n + 1)).head =
      some (bit x w 0) := by
  have hp := pair_eq n m
  have hk := K_pos n m
  calc
    (scanConfig B x w (n + 1)).tape (scanConfig B x w (n + 1)).head =
        sourceCell x w (scanConfig B x w (n + 1)).head.val := compact_read x w _
    _ = sourceCell x w (n + 1) := congrArg (sourceCell x w) (scanHead_val (le_refl _))
    _ = some (bit x w 0) := by
      unfold sourceCell
      rw [if_neg (by omega), if_pos (by omega), show n + 1 - n - 1 = 0 by omega]
private theorem fetch_read {n m B : Nat} (x : Bitstring n) (w : Bitstring m) (r : Nat) (hr : r < K n m) : (fetchConfig B x w r).tape (fetchConfig B x w r).head = some (bit x w r) := by
  calc
    (fetchConfig B x w r).tape (fetchConfig B x w r).head =
        rollCell x w r (fetchConfig B x w r).head.val := rfl
    _ = rollCell x w r (n + 1 + r) :=
      congrArg (rollCell x w r) (fetchHead_lt hr)
    _ = some (bit x w r) := roll_fetch x w r hr
private theorem carry_read {n m B : Nat} (x : Bitstring n) (w : Bitstring m) (r : Nat) (hr : r < K n m) : (carryConfig B x w r).tape (carryConfig B x w r).head = none := by
  calc
    (carryConfig B x w r).tape (carryConfig B x w r).head =
        takeCell x w r (carryConfig B x w r).head.val := rfl
    _ = takeCell x w r (n + r) := congrArg (takeCell x w r) (carryHead_val hr)
    _ = rollCell x w r (n + r) := by unfold takeCell; rw [if_neg (by omega)]
    _ = none := roll_hole x w r
private theorem hole_read {n m B : Nat} (x : Bitstring n) (w : Bitstring m) (r : Nat) (hr : r ≤ K n m) : (holeConfig B x w r).tape (holeConfig B x w r).head = none := by
  calc
    (holeConfig B x w r).tape (holeConfig B x w r).head =
        rollCell x w r (holeConfig B x w r).head.val := rfl
    _ = rollCell x w r (n + r) := congrArg (rollCell x w r) (holeHead_val hr)
    _ = none := roll_hole x w r
private theorem scan_action {n m B : Nat} (x : Bitstring n) (w : Bitstring m) (j : Nat) (hj : j < n + 1) : machine.step (scanConfig B x w j).state
      ((scanConfig B x w j).tape (scanConfig B x w j).head) =
      (qStart, none, .right) := by
  rw [scan_read x w j hj]
  rfl
private theorem scan_block_action {n m B : Nat} (x : Bitstring n) (w : Bitstring m) : machine.step (scanConfig B x w (n + 1)).state
      ((scanConfig B x w (n + 1)).tape (scanConfig B x w (n + 1)).head) =
      (carryState (bit x w 0), none, .left) := by
  rw [scan_block_read x w]
  change machine.step qStart (some (bit x w 0)) = _
  cases bit x w 0 <;> rfl
private theorem fetch_action {n m B : Nat} (x : Bitstring n) (w : Bitstring m) (r : Nat) (hr : r < K n m) : machine.step (fetchConfig B x w r).state
      ((fetchConfig B x w r).tape (fetchConfig B x w r).head) =
      (carryState (bit x w r), none, .left) := by
  rw [fetch_read x w r hr]
  change machine.step (fetchState r) (some (bit x w r)) = _
  exact fetch_some r (bit x w r)
private theorem carry_action {n m B : Nat} (x : Bitstring n) (w : Bitstring m) (r : Nat) (hr : r < K n m) : machine.step (carryConfig B x w r).state
      ((carryConfig B x w r).tape (carryConfig B x w r).head) =
      (qHole, some (bit x w r), .right) := by
  rw [carry_read x w r hr]
  change machine.step (carryState (bit x w r)) none = _
  exact carry_none (bit x w r)
private theorem hole_action {n m B : Nat} (x : Bitstring n) (w : Bitstring m) (r : Nat) (hr : r ≤ K n m) : machine.step (holeConfig B x w r).state
      ((holeConfig B x w r).tape (holeConfig B x w r).head) =
      (qFetch, none, .right) := by
  rw [hole_read x w r hr]
  exact hole_none
private theorem last_action {n m B : Nat} (x : Bitstring n) (w : Bitstring m) : machine.step (fetchConfig B x w (K n m)).state
      ((fetchConfig B x w (K n m)).tape (fetchConfig B x w (K n m)).head) =
      (qAccept, none, .stay) := by
  have hblank : (fetchConfig B x w (K n m)).tape
      (fetchConfig B x w (K n m)).head = none := by
    change rolledTape B x w (K n m) (fetchConfig B x w (K n m)).head = none
    rw [roll_last x w]
    apply shifted_above x w
    calc
      pairLength n m ≤ (finalHead n m B).val := finalHead_ge n m B
      _ = (fetchConfig B x w (K n m)).head.val := fetchHead_last.symm
  rw [hblank]
  change machine.step (fetchState (K n m)) none = _
  exact fetch_none (K_pos n m)
private theorem step_scan {n m B : Nat} (x : Bitstring n) (w : Bitstring m) (j : Nat) (hj : j < n + 1) : machine.stepConfig (scanConfig B x w j) = scanConfig B x w (j + 1) := by
  rw [stepConfig_eq _ _ _ _ (scan_action x w j hj)]
  apply config_ext
  · rfl
  · apply Fin.ext
    have h0 := scanConfig_head_val (B := B) (m := m) (x := x) (w := w)
      (by omega : j ≤ n + 1)
    have h1 := scanConfig_head_val (B := B) (m := m) (x := x) (w := w)
      (by omega : j + 1 ≤ n + 1)
    have hb : (scanConfig B x w j).head.val + 1 <
        tapeLength (pairLength n m) B := by
      unfold tapeLength pairLength
      omega
    calc
      (moveHead (scanConfig B x w j).head .right).val =
          (scanConfig B x w j).head.val + 1 := move_right_val _ hb
      _ = j + 1 := by omega
      _ = (scanConfig B x w (j + 1)).head.val := h1.symm
  · exact update_same _ _ none (scan_read x w j hj)
private theorem step_fetch {n m B : Nat} (x : Bitstring n) (w : Bitstring m) (r : Nat) (hr : r < K n m) : machine.stepConfig (fetchConfig B x w r) = carryConfig B x w r := by
  rw [stepConfig_eq _ _ _ _ (fetch_action x w r hr)]
  apply config_ext
  · rfl
  · apply Fin.ext
    have hf := fetchConfig_head_lt (B := B) (n := n) (m := m)
      (x := x) (w := w) hr
    have hc := carryConfig_head_val (B := B) (n := n) (m := m)
      (x := x) (w := w) hr
    change (fetchConfig B x w r).head.val - 1 = (carryConfig B x w r).head.val
    omega
  · exact erase_eq_taken x w r _ (fetchHead_lt hr)
private theorem step_carry {n m B : Nat} (x : Bitstring n) (w : Bitstring m) (r : Nat) (hr : r < K n m) : machine.stepConfig (carryConfig B x w r) = holeConfig B x w (r + 1) := by
  rw [stepConfig_eq _ _ _ _ (carry_action x w r hr)]
  apply config_ext
  · rfl
  · apply Fin.ext
    have hc := carryConfig_head_val (B := B) (n := n) (m := m)
      (x := x) (w := w) hr
    have hh := holeConfig_head_val (B := B) (n := n) (m := m)
      (x := x) (w := w) (by omega : r + 1 ≤ K n m)
    have hb : (carryConfig B x w r).head.val + 1 <
        tapeLength (pairLength n m) B := by
      unfold tapeLength pairLength K at *
      omega
    calc
      (moveHead (carryConfig B x w r).head .right).val =
          (carryConfig B x w r).head.val + 1 := move_right_val _ hb
      _ = n + (r + 1) := by omega
      _ = (holeConfig B x w (r + 1)).head.val := hh.symm
  · exact fill_eq_roll x w r _ (carryHead_val hr)
private theorem step_hole {n m B : Nat} (x : Bitstring n) (w : Bitstring m) (r : Nat) (hr0 : 0 < r) (hr : r ≤ K n m) : machine.stepConfig (holeConfig B x w r) = fetchConfig B x w r := by
  rw [stepConfig_eq _ _ _ _ (hole_action x w r hr)]
  apply config_ext
  · exact (fetchState_pos hr0).symm
  · apply Fin.ext
    have hh := holeConfig_head_val (B := B) (n := n) (m := m)
      (x := x) (w := w) hr
    by_cases hrlt : r < K n m
    · have hf := fetchConfig_head_lt (B := B) (n := n) (m := m)
        (x := x) (w := w) hrlt
      have hb : (holeConfig B x w r).head.val + 1 <
          tapeLength (pairLength n m) B := by
        unfold tapeLength pairLength K at *
        omega
      calc
        (moveHead (holeConfig B x w r).head .right).val =
            (holeConfig B x w r).head.val + 1 := move_right_val _ hb
        _ = n + 1 + r := by omega
        _ = (fetchConfig B x w r).head.val := hf.symm
    · have hre : r = K n m := by omega
      by_cases hB : B = 0
      · have hb : ¬(holeConfig B x w r).head.val + 1 <
            tapeLength (pairLength n m) B := by
          unfold tapeLength pairLength K at *
          omega
        unfold moveHead
        rw [dif_neg hb]
        rw [holeConfig_head_val hr, hre, fetchConfig_head_last,
          finalHead_val, if_pos hB, pair_eq]
      · have hb : (holeConfig B x w r).head.val + 1 <
            tapeLength (pairLength n m) B := by
          have hBp : 1 ≤ B := Nat.one_le_iff_ne_zero.mpr hB
          unfold tapeLength pairLength K at *
          omega
        rw [move_right_val _ hb]
        rw [holeConfig_head_val hr, hre, fetchConfig_head_last,
          finalHead_val, if_neg hB, pair_eq]
  · exact update_same _ _ none (hole_read x w r hr)
private theorem step_last {n m B : Nat} (x : Bitstring n) (w : Bitstring m) : machine.stepConfig (fetchConfig B x w (K n m)) = finalConfig B x w := by
  rw [stepConfig_eq _ _ _ _ (last_action x w)]
  apply config_ext
  · rfl
  · apply Fin.ext
    change (fetchConfig B x w (K n m)).head.val = (finalHead n m B).val
    exact fetchConfig_head_last
  · change (fun i => if i = (fetchConfig B x w (K n m)).head then none
      else rolledTape B x w (K n m) i) = shiftedTape B x w
    rw [roll_last x w]
    apply update_same
    apply shifted_above x w
    calc
      pairLength n m ≤ (finalHead n m B).val := finalHead_ge n m B
      _ = (fetchConfig B x w (K n m)).head.val := fetchHead_last.symm
private theorem run_scan {n m B : Nat} (x : Bitstring n) (w : Bitstring m) (j : Nat) (hj : j ≤ n + 1) : machine.run j (startConfig B x w) = scanConfig B x w j := by
  induction j with
  | zero =>
      apply config_ext
      · rfl
      · apply Fin.ext
        change 0 = (scanConfig B x w 0).head.val
        exact (scanHead_val (Nat.zero_le _)).symm
      · rfl
  | succ j ih =>
      rw [UniformTM.run, ih (by omega)]
      exact step_scan x w j (by omega)
private theorem scan_to_zero {n m B : Nat} (x : Bitstring n) (w : Bitstring m) : machine.run (n + 1) (startConfig B x w) = fetchConfig B x w 0 := by
  rw [run_scan x w (n + 1) (le_refl _)]
  apply config_ext
  · rfl
  · apply Fin.ext
    rw [scanConfig_head_val (x := x) (w := w) (le_refl _),
      fetchConfig_head_lt (x := x) (w := w) (K_pos n m)]
  · exact (roll_zero x w).symm
private theorem round {n m B : Nat} (x : Bitstring n) (w : Bitstring m) (r : Nat) (hr : r < K n m) : machine.run 3 (fetchConfig B x w r) = fetchConfig B x w (r + 1) := by
  change machine.stepConfig (machine.stepConfig (machine.stepConfig
    (fetchConfig B x w r))) = _
  rw [step_fetch x w r hr, step_carry x w r hr,
    step_hole x w (r + 1) (by omega) (by omega)]
private theorem roll_run {n m B : Nat} (x : Bitstring n) (w : Bitstring m) (r : Nat) (hr : r ≤ K n m) : machine.run (3 * r) (fetchConfig B x w 0) = fetchConfig B x w r := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [show 3 * (r + 1) = 3 * r + 3 by ring, machine.run_add,
        ih (by omega), round x w r (by omega)]
theorem run_exact {n m : Nat} (B : Nat) (x : Bitstring n) (w : Bitstring m) : machine.run (clock n m) (startConfig B x w) = finalConfig B x w := by
  rw [show clock n m = (n + 1) + (3 * K n m + 1) by unfold clock K; omega,
    machine.run_add, scan_to_zero x w, machine.run_add,
    roll_run x w (K n m) (le_refl _), UniformTM.run]
  exact step_last x w
theorem final_fields {n m B : Nat} (x : Bitstring n) (w : Bitstring m) : (machine.run (clock n m) (startConfig B x w)).state = qAccept ∧
    (machine.run (clock n m) (startConfig B x w)).state = machine.accept ∧
    (machine.run (clock n m) (startConfig B x w)).head.val =
      pairLength n m + Nat.min B 1 ∧
    (machine.run (clock n m) (startConfig B x w)).tape = shiftedTape B x w := by
  rw [run_exact]
  exact ⟨rfl, rfl, finalHead_min n m B, rfl⟩
private theorem run_fetch {n m B : Nat} (x : Bitstring n) (w : Bitstring m) (r : Nat) (hr : r ≤ K n m) : machine.run ((n + 1) + 3 * r) (startConfig B x w) = fetchConfig B x w r := by
  rw [machine.run_add, scan_to_zero x w, roll_run x w r hr]
private theorem run_carry {n m B : Nat} (x : Bitstring n) (w : Bitstring m) (r : Nat) (hr : r < K n m) : machine.run ((n + 1) + 3 * r + 1) (startConfig B x w) = carryConfig B x w r := by
  rw [show (n + 1) + 3 * r + 1 = ((n + 1) + 3 * r) + 1 by omega,
    UniformTM.run, run_fetch x w r (by omega), step_fetch x w r hr]
private theorem run_hole {n m B : Nat} (x : Bitstring n) (w : Bitstring m) (r : Nat) (hr : r < K n m) : machine.run ((n + 1) + 3 * r + 2) (startConfig B x w) =
      holeConfig B x w (r + 1) := by
  rw [show (n + 1) + 3 * r + 2 = ((n + 1) + 3 * r + 1) + 1 by omega,
    UniformTM.run, run_carry x w r hr, step_carry x w r hr]
private theorem mod_three (t : Nat) : ∃ r d, d ≤ 2 ∧ t = 3 * r + d := by
  refine ⟨t / 3, t % 3, ?_, ?_⟩
  · have h := Nat.mod_lt t (by decide : 0 < 3)
    omega
  · have h := Nat.mod_add_div t 3
    omega
private theorem trace {n m B : Nat} (x : Bitstring n) (w : Bitstring m) (s : Nat) (hs : s ≤ clock n m) : (∃ j, j ≤ n + 1 ∧ s = j ∧ machine.run s (startConfig B x w) = scanConfig B x w j) ∨
    (∃ r, r ≤ K n m ∧ s = (n + 1) + 3 * r ∧
      machine.run s (startConfig B x w) = fetchConfig B x w r) ∨
    (∃ r, r < K n m ∧ s = (n + 1) + 3 * r + 1 ∧
      machine.run s (startConfig B x w) = carryConfig B x w r) ∨
    (∃ r, r < K n m ∧ s = (n + 1) + 3 * r + 2 ∧
      machine.run s (startConfig B x w) = holeConfig B x w (r + 1)) ∨
    (s = clock n m ∧ machine.run s (startConfig B x w) = finalConfig B x w) := by
  by_cases hscan : s ≤ n + 1
  · exact Or.inl ⟨s, hscan, rfl, run_scan x w s hscan⟩
  by_cases hfinal : s = clock n m
  · subst s
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, run_exact B x w⟩)))
  let t := s - (n + 1)
  have hst : s = (n + 1) + t := by dsimp [t]; omega
  have ht : t ≤ 3 * K n m := by
    have hc := (clock_exact n m).1
    unfold K
    omega
  obtain ⟨r, d, hd, htd⟩ := mod_three t
  have hr : r ≤ K n m := by omega
  rcases Nat.lt_or_eq_of_le hr with hrlt | hre
  · have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
    rcases hdc with rfl | rfl | rfl
    · have he : s = (n + 1) + 3 * r := by omega
      refine Or.inr (Or.inl ⟨r, hr, he, ?_⟩)
      rw [he]
      exact run_fetch (B := B) x w r hr
    · have he : s = (n + 1) + 3 * r + 1 := by omega
      refine Or.inr (Or.inr (Or.inl ⟨r, hrlt, he, ?_⟩))
      rw [he]
      exact run_carry (B := B) x w r hrlt
    · have he : s = (n + 1) + 3 * r + 2 := by omega
      refine Or.inr (Or.inr (Or.inr (Or.inl ⟨r, hrlt, he, ?_⟩)))
      rw [he]
      exact run_hole (B := B) x w r hrlt
  · have hd0 : d = 0 := by omega
    subst d
    have he : s = (n + 1) + 3 * K n m := by omega
    refine Or.inr (Or.inl ⟨K n m, le_refl _, he, ?_⟩)
    rw [he]
    exact run_fetch (B := B) x w (K n m) (le_refl _)
theorem noEarlyTerminal {n m B : Nat} (x : Bitstring n) (w : Bitstring m) (s : Nat) (hs : s < clock n m) : (machine.run s (startConfig B x w)).state ≠ qAccept ∧
    (machine.run s (startConfig B x w)).state ≠ qReject := by
  rcases trace x w s (Nat.le_of_lt hs) with
    ⟨j, hj, _, h⟩ | ⟨r, hr, _, h⟩ | ⟨r, hr, _, h⟩ |
    ⟨r, hr, _, h⟩ | ⟨he, _⟩
  · rw [h]
    change qStart ≠ qAccept ∧ qStart ≠ qReject
    decide
  · rw [h]
    change fetchState r ≠ qAccept ∧ fetchState r ≠ qReject
    by_cases h0 : r = 0
    · rw [show fetchState r = qStart by unfold fetchState; rw [if_pos h0]]
      decide
    · rw [show fetchState r = qFetch by unfold fetchState; rw [if_neg h0]]
      decide
  · rw [h]
    change carryState (bit x w r) ≠ qAccept ∧ carryState (bit x w r) ≠ qReject
    cases bit x w r <;> decide
  · rw [h]
    change qHole ≠ qAccept ∧ qHole ≠ qReject
    decide
  · exact absurd he (Nat.ne_of_lt hs)
theorem run_after {n m B : Nat} (x : Bitstring n) (w : Bitstring m) (extra : Nat) : machine.run (clock n m + extra) (startConfig B x w) = finalConfig B x w := by
  rw [machine.run_add, run_exact,
    machine.run_accept (finalConfig B x w) rfl extra]
private theorem fetch_bound {n m B r : Nat} (hr : r ≤ K n m) : (fetchHead (n := n) (m := m) B r).val ≤ pairLength n m + 1 := by
  by_cases hlt : r < K n m
  · rw [fetchHead_lt hlt]
    have hp := pair_eq n m
    omega
  · have hre : r = K n m := by omega
    rw [hre, fetchHead_last]
    exact finalHead_le n m B
private theorem fetch_bound_zero {n m r : Nat} (hr : r ≤ K n m) : (fetchHead (n := n) (m := m) 0 r).val ≤ pairLength n m := by
  by_cases hlt : r < K n m
  · rw [fetchHead_lt hlt]
    have hp := pair_eq n m
    omega
  · have hre : r = K n m := by omega
    rw [hre, fetchHead_last, finalHead_val, if_pos rfl]
theorem footprint {n m B : Nat} (x : Bitstring n) (w : Bitstring m) : (∀ s, s ≤ clock n m →
      (machine.run s (startConfig B x w)).head.val ≤ pairLength n m + 1) ∧
    (B = 0 → ∀ s, s ≤ clock n m →
      (machine.run s (startConfig B x w)).head.val ≤ pairLength n m) ∧
    (machine.run (clock n m - 1) (startConfig B x w)).head.val =
      pairLength n m + Nat.min B 1 ∧
    (∀ s, s ≤ clock n m → ∀ i : Fin (tapeLength (pairLength n m) B),
      pairLength n m < i.val →
      (machine.run s (startConfig B x w)).tape i = none) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs
    rcases trace x w s hs with
      ⟨j, hj, _, h⟩ | ⟨r, hr, _, h⟩ | ⟨r, hr, _, h⟩ |
      ⟨r, hr, _, h⟩ | ⟨_, h⟩
    · rw [h, scanConfig_head_val (x := x) (w := w) hj]
      have hp := pair_eq n m
      have hk := K_pos n m
      omega
    · rw [h]
      exact fetch_bound hr
    · rw [h, carryConfig_head_val (x := x) (w := w) hr]
      have hp := pair_eq n m
      omega
    · rw [h, holeConfig_head_val (x := x) (w := w)
        (by omega : r + 1 ≤ K n m)]
      have hp := pair_eq n m
      omega
    · rw [h]
      exact finalHead_le n m B
  · intro hB s hs
    subst B
    rcases trace x w s hs with
      ⟨j, hj, _, h⟩ | ⟨r, hr, _, h⟩ | ⟨r, hr, _, h⟩ |
      ⟨r, hr, _, h⟩ | ⟨_, h⟩
    · rw [h, scanConfig_head_val (x := x) (w := w) hj]
      have hp := pair_eq n m
      have hk := K_pos n m
      omega
    · rw [h]
      exact fetch_bound_zero hr
    · rw [h, carryConfig_head_val (x := x) (w := w) hr]
      have hp := pair_eq n m
      omega
    · rw [h, holeConfig_head_val (x := x) (w := w)
        (by omega : r + 1 ≤ K n m)]
      have hp := pair_eq n m
      omega
    · rw [h]
      change (finalHead n m 0).val ≤ pairLength n m
      rw [finalHead_val, if_pos rfl]
  · have ht : clock n m - 1 = (n + 1) + 3 * K n m := by
      unfold clock K
      omega
    rw [ht, run_fetch (B := B) x w (K n m) (le_refl _),
      fetchConfig_head_last]
    exact finalHead_min n m B
  · intro s hs i hi
    rcases trace x w s hs with
      ⟨j, hj, _, h⟩ | ⟨r, hr, _, h⟩ | ⟨r, hr, _, h⟩ |
      ⟨r, hr, _, h⟩ | ⟨_, h⟩
    · rw [h]
      exact compact_right x w i hi
    · rw [h]
      exact rolled_above x w r hr i hi
    · rw [h]
      change takeCell x w r i.val = none
      unfold takeCell
      by_cases he : i.val = n + r + 1
      · rw [if_pos he]
      · rw [if_neg he]
        exact roll_above x w r i.val (by omega) hi
    · rw [h]
      exact rolled_above x w (r + 1) (by omega) i hi
    · rw [h]
      exact shifted_above x w i (by omega)
private theorem last_hole {n m B : Nat} (x : Bitstring n) (w : Bitstring m) : machine.run (clock n m - 2) (startConfig B x w) = holeConfig B x w (K n m) := by
  have hk := K_pos n m
  have h := run_hole (B := B) x w (K n m - 1) (by omega)
  have ht : clock n m - 2 = (n + 1) + 3 * (K n m - 1) + 2 := by
    unfold clock K
    omega
  rw [ht]
  have hr : K n m - 1 + 1 = K n m := by omega
  rw [hr] at h
  exact h
theorem clamps {n m B : Nat} (x : Bitstring n) (w : Bitstring m) : (∀ s, s < clock n m →
      let c := machine.run s (startConfig B x w)
      (machine.step c.state (c.tape c.head)).2.2 = .left → 0 < c.head.val) ∧
    (∀ s, s < clock n m → s ≠ clock n m - 2 →
      let c := machine.run s (startConfig B x w)
      (machine.step c.state (c.tape c.head)).2.2 = .right →
        c.head.val + 1 < tapeLength (pairLength n m) B) ∧
    (machine.run (clock n m - 2) (startConfig B x w)).head.val =
        pairLength n m ∧
    (machine.step
        (machine.run (clock n m - 2) (startConfig B x w)).state
        ((machine.run (clock n m - 2) (startConfig B x w)).tape
          (machine.run (clock n m - 2) (startConfig B x w)).head)).2.2 =
      .right ∧
    (moveHead (machine.run (clock n m - 2) (startConfig B x w)).head
        .right = (machine.run (clock n m - 2) (startConfig B x w)).head ↔
      B = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    dsimp
    rcases trace x w s (Nat.le_of_lt hs) with
      ⟨j, hj, _, h⟩ | ⟨r, hr, _, h⟩ | ⟨r, hr, _, h⟩ |
      ⟨r, hr, _, h⟩ | ⟨he, _⟩
    · rw [h]
      by_cases hj' : j < n + 1
      · rw [scan_action x w j hj']
        intro hm
        cases hm
      · intro _
        rw [scanConfig_head_val (x := x) (w := w) hj]
        omega
    · rw [h]
      by_cases hr' : r < K n m
      · rw [fetch_action x w r hr']
        intro _
        rw [fetchConfig_head_lt (x := x) (w := w) hr']
        omega
      · have hre : r = K n m := by omega
        rw [hre, last_action x w]
        intro hm
        cases hm
    · rw [h, carry_action x w r hr]
      intro hm
      cases hm
    · rw [h, hole_action x w (r + 1) (by omega)]
      intro hm
      cases hm
    · exact absurd he (Nat.ne_of_lt hs)
  · intro s hs hne
    dsimp
    rcases trace x w s (Nat.le_of_lt hs) with
      ⟨j, hj, _, h⟩ | ⟨r, hr, _, h⟩ | ⟨r, hr, _, h⟩ |
      ⟨r, hr, ht, h⟩ | ⟨he, _⟩
    · rw [h]
      by_cases hj' : j < n + 1
      · rw [scan_action x w j hj']
        intro _
        rw [scanConfig_head_val (x := x) (w := w) hj]
        have hp := pair_eq n m
        have hk := K_pos n m
        unfold tapeLength
        omega
      · have hj0 : j = n + 1 := by omega
        rw [hj0, scan_block_action x w]
        intro hm
        cases hm
    · rw [h]
      by_cases hr' : r < K n m
      · rw [fetch_action x w r hr']
        intro hm
        cases hm
      · have hre : r = K n m := by omega
        rw [hre, last_action x w]
        intro hm
        cases hm
    · rw [h, carry_action x w r hr]
      intro _
      rw [carryConfig_head_val (x := x) (w := w) hr]
      have hp := pair_eq n m
      unfold tapeLength
      omega
    · rw [h, hole_action x w (r + 1) (by omega)]
      intro _
      have hr' : r + 1 < K n m := by
        by_contra hn
        have hre : r + 1 = K n m := by omega
        apply hne
        unfold clock K at *
        omega
      rw [holeConfig_head_val (x := x) (w := w)
        (by omega : r + 1 ≤ K n m)]
      have hp := pair_eq n m
      unfold tapeLength
      omega
    · exact absurd he (Nat.ne_of_lt hs)
  · rw [last_hole x w]
    have hread := hole_read (B := B) x w (K n m) (le_refl _)
    rw [hread]
    refine ⟨?_, rfl, ?_⟩
    · rw [holeConfig_head_val (x := x) (w := w) (le_refl _)]
      exact (pair_eq n m).symm
    · constructor
      · intro he
        by_contra hB
        have hBp : 1 ≤ B := Nat.one_le_iff_ne_zero.mpr hB
        have hh := holeConfig_head_val (B := B) (n := n) (m := m)
          (x := x) (w := w) (le_refl (K n m))
        have hp := pair_eq n m
        have hb : (holeConfig B x w (K n m)).head.val + 1 <
            tapeLength (pairLength n m) B := by
          unfold tapeLength
          omega
        have hv := congrArg Fin.val he
        rw [move_right_val _ hb] at hv
        omega
      · intro hB
        subst B
        have hh := holeConfig_head_val (B := 0) (n := n) (m := m)
          (x := x) (w := w) (le_refl (K n m))
        have hp := pair_eq n m
        have hb : ¬(holeConfig 0 x w (K n m)).head.val + 1 <
            tapeLength (pairLength n m) 0 := by
          unfold tapeLength
          omega
        unfold moveHead
        rw [dif_neg hb]
private theorem source_budget {n m : Nat} (B B' : Nat) (x : Bitstring n) (w : Bitstring m) (i : Fin (tapeLength (pairLength n m) B)) (i' : Fin (tapeLength (pairLength n m) B')) (hii : i.val = i'.val) : FixedPairTagRemoval.compactTape B x w i =
      FixedPairTagRemoval.compactTape B' x w i' := by
  calc
    FixedPairTagRemoval.compactTape B x w i = sourceCell x w i.val := compact_read x w i
    _ = sourceCell x w i'.val := congrArg (sourceCell x w) hii
    _ = FixedPairTagRemoval.compactTape B' x w i' := (compact_read x w i').symm
private theorem roll_budget {n m : Nat} (B B' : Nat) (x : Bitstring n) (w : Bitstring m) (r : Nat) (i : Fin (tapeLength (pairLength n m) B)) (i' : Fin (tapeLength (pairLength n m) B')) (hii : i.val = i'.val) : rolledTape B x w r i = rolledTape B' x w r i' :=
  congrArg (rollCell x w r) hii
private theorem take_budget {n m : Nat} (B B' : Nat) (x : Bitstring n) (w : Bitstring m) (r : Nat) (i : Fin (tapeLength (pairLength n m) B)) (i' : Fin (tapeLength (pairLength n m) B')) (hii : i.val = i'.val) : takenTape B x w r i = takenTape B' x w r i' :=
  congrArg (takeCell x w r) hii
private theorem final_budget {n m : Nat} (B B' : Nat) (x : Bitstring n) (w : Bitstring m) (i : Fin (tapeLength (pairLength n m) B)) (i' : Fin (tapeLength (pairLength n m) B')) (hii : i.val = i'.val) : shiftedTape B x w i = shiftedTape B' x w i' :=
  congrArg (finalCell x w) hii
theorem budget_accounting {n m : Nat} (B B' : Nat) (x : Bitstring n) (w : Bitstring m) (hscope : B = 0 ↔ B' = 0) (s : Nat) (hs : s ≤ clock n m) : (machine.run s (startConfig B x w)).state =
      (machine.run s (startConfig B' x w)).state ∧
    (machine.run s (startConfig B x w)).head.val =
      (machine.run s (startConfig B' x w)).head.val ∧
    (∀ (i : Fin (tapeLength (pairLength n m) B))
        (i' : Fin (tapeLength (pairLength n m) B')), i.val = i'.val →
      (machine.run s (startConfig B x w)).tape i =
        (machine.run s (startConfig B' x w)).tape i') := by
  rcases trace (B := B) x w s hs with
    ⟨j, hj, ht, h⟩ | ⟨r, hr, ht, h⟩ | ⟨r, hr, ht, h⟩ |
    ⟨r, hr, ht, h⟩ | ⟨ht, h⟩
  · subst s
    have h' := run_scan (B := B') x w j hj
    rw [h, h']
    refine ⟨rfl, ?_, fun i i' hii => source_budget B B' x w i i' hii⟩
    rw [scanConfig_head_val (B := B) (x := x) (w := w) hj,
      scanConfig_head_val (B := B') (x := x) (w := w) hj]
  · subst s
    have h' := run_fetch (B := B') x w r hr
    rw [h, h']
    refine ⟨rfl, ?_, fun i i' hii => roll_budget B B' x w r i i' hii⟩
    by_cases hlt : r < K n m
    · rw [fetchConfig_head_lt (B := B) (x := x) (w := w) hlt,
        fetchConfig_head_lt (B := B') (x := x) (w := w) hlt]
    · have hre : r = K n m := by omega
      rw [hre, fetchConfig_head_last (B := B) (x := x) (w := w),
        fetchConfig_head_last (B := B') (x := x) (w := w)]
      exact finalHead_scope hscope
  · subst s
    have h' := run_carry (B := B') x w r hr
    rw [h, h']
    refine ⟨rfl, ?_, fun i i' hii => take_budget B B' x w r i i' hii⟩
    rw [carryConfig_head_val (B := B) (x := x) (w := w) hr,
      carryConfig_head_val (B := B') (x := x) (w := w) hr]
  · subst s
    have h' := run_hole (B := B') x w r hr
    rw [h, h']
    refine ⟨rfl, ?_, fun i i' hii => roll_budget B B' x w (r + 1) i i' hii⟩
    rw [holeConfig_head_val (B := B) (x := x) (w := w)
        (by omega : r + 1 ≤ K n m),
      holeConfig_head_val (B := B') (x := x) (w := w)
        (by omega : r + 1 ≤ K n m)]
  · subst s
    have h' := run_exact B' x w
    rw [h, h']
    refine ⟨rfl, finalHead_scope hscope, fun i i' hii => final_budget B B' x w i i' hii⟩
private theorem final_left {n m : Nat} (x : Bitstring n) (w : Bitstring m)
    (k : Nat) (hk : k < n) : finalCell x w k = none := by
  unfold finalCell
  rw [if_neg (by omega)]
private theorem final_x {n m : Nat} (x : Bitstring n) (w : Bitstring m) (j : Fin n) : finalCell x w (n + j.val) = some (x j) := by
  unfold finalCell
  rw [if_pos (by unfold pairLength; omega),
    show n + j.val - n = j.val by omega, bit_x x w j]
private theorem final_w {n m : Nat} (x : Bitstring n) (w : Bitstring m) (j : Fin m) : finalCell x w (2 * n + j.val) = some (w j) := by
  have hp := pair_eq n m
  unfold finalCell
  rw [if_pos (by unfold K at hp; omega),
    show 2 * n + j.val - n = n + j.val by omega, bit_w x w j]
private theorem final_marker {n m : Nat} (x : Bitstring n) (w : Bitstring m) : finalCell x w (2 * n + m) = some true := by
  have hp := pair_eq n m
  unfold finalCell
  rw [if_pos (by unfold K at hp; omega),
    show 2 * n + m - n = n + m by omega, bit_marker]
private theorem final_append {n m : Nat} (x : Bitstring n) (w : Bitstring m)
    (j : Fin (n + m)) : finalCell x w (n + j.val) = some (Fin.append x w j) := by
  have hp := pair_eq n m
  unfold K at hp
  unfold finalCell
  rw [if_pos (by omega), show n + j.val - n = j.val by omega,
    bit_append x w j]
theorem final_layout {n m B : Nat} (x : Bitstring n) (w : Bitstring m) : let c := machine.run (clock n m) (startConfig B x w)
    (∀ i : Fin (tapeLength (pairLength n m) B), i.val < n → c.tape i = none) ∧
    (∀ j : Fin n, c.tape ⟨n + j.val, by unfold tapeLength pairLength; omega⟩ =
      some (x j)) ∧
    (∀ j : Fin m, c.tape ⟨2 * n + j.val, by unfold tapeLength pairLength; omega⟩ =
      some (w j)) ∧
    c.tape ⟨2 * n + m, by unfold tapeLength pairLength; omega⟩ = some true ∧
    (∀ i : Fin (tapeLength (pairLength n m) B),
      pairLength n m ≤ i.val → c.tape i = none) := by
  dsimp
  rw [run_exact]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact final_left x w i.val hi
  · intro j
    exact final_x x w j
  · intro j
    exact final_w x w j
  · exact final_marker x w
  · exact shifted_above x w
private theorem recover_nat {n m : Nat} (x : Bitstring n) (w : Bitstring m)
    (k : Nat) : sourceCell x w k =
      if k = 0 then none else finalCell x w (k - 1) := by
  by_cases h0 : k = 0
  · subst k
    simp [sourceCell]
  · rw [if_neg h0]
    unfold sourceCell
    by_cases hl : k ≤ n
    · rw [if_pos hl]
      unfold finalCell
      rw [if_neg (by omega)]
    · rw [if_neg hl]
      by_cases hp : k ≤ pairLength n m
      · rw [if_pos hp]
        unfold finalCell
        rw [if_pos (by omega), show k - 1 - n = k - n - 1 by omega]
      · rw [if_neg hp]
        unfold finalCell
        rw [if_neg (by omega)]
private theorem recover_cell {n m B : Nat} (x : Bitstring n) (w : Bitstring m) (i : Fin (tapeLength (pairLength n m) B)) : FixedPairTagRemoval.compactTape B x w i =
      if i.val = 0 then none else shiftedTape B x w
        ⟨i.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le i.val 1) i.isLt⟩ := by
  rw [compact_read]
  change sourceCell x w i.val =
    if i.val = 0 then none else finalCell x w (i.val - 1)
  exact recover_nat x w i.val
theorem recovery {n m B : Nat} (x : Bitstring n) (w : Bitstring m) : (∀ i : Fin (tapeLength (pairLength n m) B),
      FixedPairTagRemoval.compactTape B x w i =
        if i.val = 0 then none else shiftedTape B x w
          ⟨i.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le i.val 1) i.isLt⟩) ∧
    (∀ (x' : Bitstring n) (w' : Bitstring m),
      shiftedTape B x w = shiftedTape B x' w' →
      FixedPairTagRemoval.compactTape B x w =
        FixedPairTagRemoval.compactTape B x' w') := by
  refine ⟨recover_cell x w, ?_⟩
  intro x' w' hout
  funext i
  rw [recover_cell x w i, recover_cell x' w' i]
  by_cases h0 : i.val = 0
  · rw [if_pos h0, if_pos h0]
  · rw [if_neg h0, if_neg h0, hout]
theorem phase_contract {n m B : Nat} (x : Bitstring n) (w : Bitstring m) : let c0 := startConfig B x w
    c0.head = (FixedPairTagRemoval.finalConfig B x w).head ∧
    c0.tape = (FixedPairTagRemoval.finalConfig B x w).tape ∧
    machine.run (clock n m) c0 = finalConfig B x w ∧
    (∀ s, s < clock n m →
      (machine.run s c0).state ≠ qAccept ∧ (machine.run s c0).state ≠ qReject) ∧
    (∀ s, s ≤ clock n m →
      (machine.run s c0).head.val ≤ pairLength n m + 1) ∧
    (machine.run (clock n m) c0).head.val = pairLength n m + Nat.min B 1 ∧
    (∀ j : Fin (n + m), (machine.run (clock n m) c0).tape
      ⟨n + j.val, by unfold tapeLength pairLength; omega⟩ =
        some (Fin.append x w j)) ∧
    (machine.run (clock n m) c0).tape
      ⟨2 * n + m, by unfold tapeLength pairLength; omega⟩ = some true ∧
    FixedPairTagRemoval.compactTape B x w = fun i =>
      if i.val = 0 then none else shiftedTape B x w
        ⟨i.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le i.val 1) i.isLt⟩ := by
  dsimp
  refine ⟨rfl, rfl, run_exact B x w, fun s hs => noEarlyTerminal x w s hs,
    (footprint x w).1, (final_fields x w).2.2.1, ?_,
    (final_layout x w).2.2.2.1, ?_⟩
  · intro j
    rw [run_exact]
    exact final_append x w j
  · funext i
    exact recover_cell x w i
end FixedPairOriginShiftBootstrap
end Pnp3.Complexity.Uniform.V1
