import Complexity.Uniform.V1.FixedPairContentMarkerErase
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
namespace Pnp3.Complexity.Uniform.V1
namespace FixedContentTagGate
open PairEncoding
abbrev stateCount : Nat := 15
private def qStart : Fin stateCount := ⟨0, by decide⟩
private def qProbe : Fin stateCount := ⟨1, by decide⟩
private def qCheckF : Fin stateCount := ⟨2, by decide⟩
private def qCheckT : Fin stateCount := ⟨3, by decide⟩
private def qReturnF : Fin stateCount := ⟨4, by decide⟩
private def qReturnT : Fin stateCount := ⟨5, by decide⟩
private def qTag (j : Fin 7) : Fin stateCount := ⟨6 + j.1, by change 6 + j.1 < 15; omega⟩
private def qAccept : Fin stateCount := ⟨13, by decide⟩
private def qReject : Fin stateCount := ⟨14, by decide⟩
def expectedTagBit (j : Fin 8) : Bool := match j.1 with | 0 => true | 1 => false | 2 => true | 3 => true | 4 => false | 5 => false | 6 => true | _ => false
def physicalSymbol {L : Nat} (z : Bitstring L) (j : Nat) : Option Bool := if h : j < L then some (z ⟨j, h⟩) else none
private def badIndex {L : Nat} (z : Bitstring L) : Nat := if physicalSymbol z 0 = some true then if physicalSymbol z 1 = some false then if physicalSymbol z 2 = some true then if physicalSymbol z 3 = some true then if physicalSymbol z 4 = some false then if physicalSymbol z 5 = some false then if physicalSymbol z 6 = some true then if physicalSymbol z 7 = some false then 8 else 7 else 6 else 5 else 4 else 3 else 2 else 1 else 0
def tagMatches {L : Nat} (z : Bitstring L) : Bool := decide (badIndex z = 8)
private def raw (q : Fin stateCount) (scanned : Option Bool) : Fin stateCount × Option Bool × Move := match q.1 with
  | 0 => match scanned with | none => (qProbe, none, .left) | some b => (qReject, some b, .stay)
  | 1 => match scanned with | none => (qReject, none, .stay) | some false => (qCheckF, none, .left) | some true => (qCheckT, none, .left)
  | 2 => match scanned with | none => (qReject, some false, .stay) | some b => (qReturnF, some b, .right)
  | 3 => match scanned with | none => (qTag ⟨0, by decide⟩, some true, .right) | some b => (qReturnT, some b, .right)
  | 4 => match scanned with | none => (qProbe, some false, .left) | some b => (qReject, some b, .stay)
  | 5 => match scanned with | none => (qProbe, some true, .left) | some b => (qReject, some b, .stay)
  | 6 =>
      match scanned with | some false => (qTag ⟨1, by decide⟩, some false, .right) | s => (qReject, s, .stay)
  | 7 =>
      match scanned with | some true => (qTag ⟨2, by decide⟩, some true, .right) | s => (qReject, s, .stay)
  | 8 =>
      match scanned with | some true => (qTag ⟨3, by decide⟩, some true, .right) | s => (qReject, s, .stay)
  | 9 =>
      match scanned with | some false => (qTag ⟨4, by decide⟩, some false, .right) | s => (qReject, s, .stay)
  | 10 =>
      match scanned with | some false => (qTag ⟨5, by decide⟩, some false, .right) | s => (qReject, s, .stay)
  | 11 =>
      match scanned with | some true => (qTag ⟨6, by decide⟩, some true, .right) | s => (qReject, s, .stay)
  | 12 =>
      match scanned with | some false => (qAccept, some false, .right) | s => (qReject, s, .stay)
  | 13 => (qAccept, scanned, .stay)
  | _ => (qReject, scanned, .stay)
def machine : UniformTM where
  stateCount := stateCount
  start := qStart
  accept := qAccept
  reject := qReject
  accept_ne_reject := by decide
  rawStep := raw
def startConfig {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) : Config stateCount (pairLength a m) B where
  state := qStart
  head := (FixedPairContentMarkerErase.finalConfig B x w).head
  tape := (FixedPairContentMarkerErase.finalConfig B x w).tape
def deadline (a m : Nat) : Nat := 3 * (a + m) + 7
def finalConfig {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) : Config stateCount (pairLength a m) B where
  state := if tagMatches (Fin.append x w) then qAccept else qReject
  head := ⟨min (badIndex (Fin.append x w)) (a + m), by unfold tapeLength pairLength; omega⟩
  tape := FixedPairContentMarkerErase.contentTape B x w
private theorem badIndex_le_eight {L : Nat} (z : Bitstring L) : badIndex z ≤ 8 := by
  unfold badIndex
  split <;> try omega
  split <;> try omega
  split <;> try omega
  split <;> try omega
  split <;> try omega
  split <;> try omega
  split <;> try omega
  split <;> omega
private theorem badIndex_eq_eight_iff {L : Nat} (z : Bitstring L) : badIndex z = 8 ↔ ∀ j : Fin 8, physicalSymbol z j.1 = some (expectedTagBit j) := by
  unfold badIndex
  constructor
  · intro h
    split at h <;> try omega
    split at h <;> try omega
    split at h <;> try omega
    split at h <;> try omega
    split at h <;> try omega
    split at h <;> try omega
    split at h <;> try omega
    split at h <;> try omega
    intro j
    fin_cases j <;> simp_all [expectedTagBit]
  · intro h
    have h0 := h ⟨0, by decide⟩; have h1 := h ⟨1, by decide⟩
    have h2 := h ⟨2, by decide⟩; have h3 := h ⟨3, by decide⟩
    have h4 := h ⟨4, by decide⟩; have h5 := h ⟨5, by decide⟩
    have h6 := h ⟨6, by decide⟩; have h7 := h ⟨7, by decide⟩
    simp [h0, h1, h2, h3, h4, h5, h6, h7, expectedTagBit]
private theorem badIndex_lt_specs {L : Nat} (z : Bitstring L)
    (h : badIndex z < 8) : physicalSymbol z (badIndex z) ≠
        some (expectedTagBit ⟨badIndex z, h⟩) ∧ ∀ i : Fin 8, i.1 < badIndex z → physicalSymbol z i.1 = some (expectedTagBit i) := by
  unfold badIndex at h ⊢
  split <;> rename_i h0
  split <;> rename_i h1
  split <;> rename_i h2
  split <;> rename_i h3
  split <;> rename_i h4
  split <;> rename_i h5
  split <;> rename_i h6
  split <;> rename_i h7
  all_goals try { simp [h0, h1, h2, h3, h4, h5, h6, h7] at h }
  all_goals simp_all [expectedTagBit]
  all_goals intro i hi; fin_cases i <;> simp_all
private theorem physical_present_lt {L : Nat} (z : Bitstring L) (j : Nat) (b : Bool) (h : physicalSymbol z j = some b) : j < L := by
  unfold physicalSymbol at h
  split at h
  · assumption
  · simp at h
private theorem badIndex_le_length {L : Nat} (z : Bitstring L) (hL : 0 < L) : badIndex z ≤ L := by
  by_cases h8 : badIndex z = 8
  · have hall := (badIndex_eq_eight_iff z).1 h8
    have h7 := physical_present_lt _ _ _ (hall ⟨7, by decide⟩)
    change 7 < L at h7
    rw [h8]
    omega
  · have hb : badIndex z < 8 := by
      have := badIndex_le_eight z
      omega
    by_cases h0 : badIndex z = 0
    · omega
    · let i : Fin 8 := ⟨badIndex z - 1, by omega⟩
      have hp := (badIndex_lt_specs z hb).2 i (by dsimp [i]; omega)
      have hi := physical_present_lt _ _ _ hp
      dsimp [i] at hi
      omega
theorem tag_contract {L : Nat} (z : Bitstring L) : expectedTagBit ⟨0, by decide⟩ = true ∧ expectedTagBit ⟨1, by decide⟩ = false ∧ expectedTagBit ⟨2, by decide⟩ = true ∧ expectedTagBit ⟨3, by decide⟩ = true ∧ expectedTagBit ⟨4, by decide⟩ = false ∧ expectedTagBit ⟨5, by decide⟩ = false ∧ expectedTagBit ⟨6, by decide⟩ = true ∧ expectedTagBit ⟨7, by decide⟩ = false ∧ (tagMatches z = true ↔
      ∀ j : Fin 8, physicalSymbol z j.1 = some (expectedTagBit j)) ∧ (tagMatches z = true → 8 ≤ L) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · simp [tagMatches, badIndex_eq_eight_iff]
  · intro h
    have hall := (badIndex_eq_eight_iff z).mp (by simpa [tagMatches] using h)
    have h7 := hall ⟨7, by decide⟩
    unfold physicalSymbol at h7
    split at h7
    · rename_i hlt
      change 7 < L at hlt
      omega
    · simp at h7
theorem table_and_resource_pins : machine.rawStep = raw ∧ machine.stateCount = 15 ∧ machine.start = ⟨0, by decide⟩ ∧ machine.accept = ⟨13, by decide⟩ ∧ machine.reject = ⟨14, by decide⟩ ∧ machine.accept.val = 13 ∧ machine.reject.val = 14 ∧ Fintype.card (Fin machine.stateCount × Option Bool) = 45 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  change Fintype.card (Fin 15 × Option Bool) = 45
  decide
private theorem config_ext {N B : Nat} {c d : Config stateCount N B} (hs : c.state = d.state) (hh : c.head = d.head) (ht : c.tape = d.tape) : c = d := by
  cases c; cases d; cases hs; cases hh; cases ht
  rfl
private theorem step_eq {N B : Nat} (c : Config stateCount N B) (q' : Fin stateCount) (s' : Option Bool) (mv : Move) (ha : machine.step c.state (c.tape c.head) = (q', s', mv)) : machine.stepConfig c = ({ state := q', head := moveHead c.head mv, tape := fun i => if i = c.head then s' else c.tape i } : Config stateCount N B) := by
  apply config_ext
  · change (machine.step c.state (c.tape c.head)).1 = q'
    rw [ha]
  · change moveHead c.head (machine.step c.state (c.tape c.head)).2.2 = _
    rw [ha]
  · funext i
    change (if i = c.head then (machine.step c.state (c.tape c.head)).2.1
      else c.tape i) = _
    rw [ha]
private theorem step_keep {N B : Nat} (c : Config stateCount N B) (q' : Fin stateCount) (mv : Move) (ha : machine.step c.state (c.tape c.head) = (q', c.tape c.head, mv)) : machine.stepConfig c = ({ state := q', head := moveHead c.head mv, tape := c.tape } : Config stateCount N B) := by
  apply config_ext
  · change (machine.step c.state (c.tape c.head)).1 = q'
    rw [ha]
  · change moveHead c.head (machine.step c.state (c.tape c.head)).2.2 = _
    rw [ha]
  · funext i
    change (if i = c.head then (machine.step c.state (c.tape c.head)).2.1
      else c.tape i) = c.tape i
    rw [ha]
    by_cases hi : i = c.head <;> simp [hi]
private def content {a m : Nat} (x : Bitstring a) (w : Bitstring m) : Bitstring (a + m) := Fin.append x w
private def baseTape {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) := FixedPairContentMarkerErase.contentTape B x w
private def erasedTape {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) (k : Nat) : Fin (tapeLength (pairLength a m) B) → Option Bool := fun i => if i.1 = k then none else baseTape B x w i
private def probeConfig {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) (k : Nat) (hk : k ≤ a + m) : Config stateCount (pairLength a m) B where
  state := qProbe
  head := ⟨k, by unfold tapeLength pairLength; omega⟩
  tape := baseTape B x w
private def checkConfig {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) (k : Nat) (hk : k < a + m) : Config stateCount (pairLength a m) B where
  state := if (content x w) ⟨k, hk⟩ then qCheckT else qCheckF
  head := ⟨k - 1, by unfold tapeLength pairLength; omega⟩
  tape := erasedTape B x w k
private def returnConfig {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) (k : Nat) (hk : k < a + m) : Config stateCount (pairLength a m) B where
  state := if (content x w) ⟨k, hk⟩ then qReturnT else qReturnF
  head := ⟨k, by unfold tapeLength pairLength; omega⟩
  tape := erasedTape B x w k
private theorem base_read {a m B : Nat} (x : Bitstring a) (w : Bitstring m) {k : Nat} (hk : k < a + m) : baseTape B x w ⟨k, by unfold tapeLength pairLength; omega⟩ = some ((content x w) ⟨k, hk⟩) := by
  simp [baseTape, FixedPairContentMarkerErase.contentTape, hk, content]
private theorem base_blank {a m B : Nat} (x : Bitstring a) (w : Bitstring m) {k : Nat} (hk : a + m ≤ k)
    (hfit : k < tapeLength (pairLength a m) B) : baseTape B x w ⟨k, hfit⟩ = none := by
  simp [baseTape, FixedPairContentMarkerErase.contentTape, Nat.not_lt_of_ge hk]
private theorem erased_same {a m B : Nat} (x : Bitstring a) (w : Bitstring m) (k : Nat) (i : Fin (tapeLength (pairLength a m) B)) (hi : i.1 ≠ k) : erasedTape B x w k i = baseTape B x w i := by simp [erasedTape, hi]
private theorem erased_here {a m B : Nat} (x : Bitstring a) (w : Bitstring m) (k : Nat) (hk : k < tapeLength (pairLength a m) B) : erasedTape B x w k ⟨k, hk⟩ = none := by simp [erasedTape]
private def tagConfig {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) (j : Nat) (hj1 : 1 ≤ j) (hj7 : j ≤ 7) (hjL : j ≤ a + m) : Config stateCount (pairLength a m) B where
  state := qTag ⟨j - 1, by omega⟩
  head := ⟨j, by unfold tapeLength pairLength; omega⟩
  tape := baseTape B x w
private def rejectConfig {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) (j : Nat) (hj : j ≤ a + m) : Config stateCount (pairLength a m) B where
  state := qReject
  head := ⟨j, by unfold tapeLength pairLength; omega⟩
  tape := baseTape B x w
private def acceptConfig {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) (hL : 8 ≤ a + m) : Config stateCount (pairLength a m) B where
  state := qAccept
  head := ⟨8, by unfold tapeLength pairLength; omega⟩
  tape := baseTape B x w
private theorem step_start {a m B : Nat} (x : Bitstring a) (w : Bitstring m) : machine.stepConfig (startConfig B x w) = probeConfig B x w (a + m - 1) (by omega) := by
  have hread : (startConfig B x w).tape (startConfig B x w).head = none := by
    exact base_blank x w (le_refl _) (by unfold tapeLength pairLength; omega)
  have ha : machine.step (startConfig B x w).state
      ((startConfig B x w).tape (startConfig B x w).head) = (qProbe, (startConfig B x w).tape (startConfig B x w).head, .left) := by
    rw [hread]
    rfl
  rw [step_keep (startConfig B x w) qProbe .left ha]
  apply config_ext
  · rfl
  · apply Fin.ext
    rfl
  · rfl
private theorem step_probe {a m B : Nat} (x : Bitstring a) (w : Bitstring m) (k : Nat) (hk : k < a + m) : machine.stepConfig (probeConfig B x w k (Nat.le_of_lt hk)) = checkConfig B x w k hk := by
  let c := probeConfig B x w k (Nat.le_of_lt hk)
  have hread : c.tape c.head = some ((content x w) ⟨k, hk⟩) := base_read x w hk
  have ha : machine.step c.state (c.tape c.head) = ((if (content x w) ⟨k, hk⟩ then qCheckT else qCheckF), none, .left) := by
    rw [hread]
    dsimp [c, probeConfig]
    cases (content x w) ⟨k, hk⟩ <;> rfl
  rw [step_eq c _ none .left ha]
  apply config_ext
  · rfl
  · apply Fin.ext
    rfl
  · funext i
    dsimp [c, probeConfig]
    change (if i = (⟨k, _⟩ : Fin (tapeLength (pairLength a m) B)) then none
      else baseTape B x w i) = erasedTape B x w k i
    unfold erasedTape
    by_cases hv : i.1 = k
    · rw [if_pos hv, if_pos (Fin.ext hv)]
    · rw [if_neg hv, if_neg (fun h => hv (congrArg Fin.val h))]
private theorem step_check_pos {a m B : Nat} (x : Bitstring a) (w : Bitstring m) (k : Nat) (hk : k < a + m) (hpos : 0 < k) : machine.stepConfig (checkConfig B x w k hk) = returnConfig B x w k hk := by
  let c := checkConfig B x w k hk
  have hne : k - 1 ≠ k := by omega
  have hread : c.tape c.head = some ((content x w) ⟨k - 1, by omega⟩) := by
    change erasedTape B x w k ⟨k - 1, _⟩ = _
    rw [erased_same x w k _ hne]
    exact base_read x w (by omega)
  have ha : machine.step c.state (c.tape c.head) = ((if (content x w) ⟨k, hk⟩ then qReturnT else qReturnF), c.tape c.head, .right) := by
    rw [hread]
    dsimp [c, checkConfig]
    cases (content x w) ⟨k, hk⟩ <;>
      cases (content x w) ⟨k - 1, by omega⟩ <;> rfl
  rw [step_keep c _ .right ha]
  apply config_ext
  · rfl
  · apply Fin.ext
    change (moveHead (⟨k - 1, _⟩ : Fin (tapeLength (pairLength a m) B)) .right).1 = k
    simp [moveHead, show k - 1 + 1 = k by omega, show k < tapeLength (pairLength a m) B by
        unfold tapeLength pairLength; omega]
  · rfl
private theorem step_return {a m B : Nat} (x : Bitstring a) (w : Bitstring m) (k : Nat) (hk : k < a + m) (hpos : 0 < k) : machine.stepConfig (returnConfig B x w k hk) = probeConfig B x w (k - 1) (by omega) := by
  let c := returnConfig B x w k hk
  have hread : c.tape c.head = none := erased_here x w k (by
    unfold tapeLength pairLength
    omega)
  have ha : machine.step c.state (c.tape c.head) = (qProbe, some ((content x w) ⟨k, hk⟩), .left) := by
    rw [hread]
    dsimp [c, returnConfig]
    cases (content x w) ⟨k, hk⟩ <;> rfl
  rw [step_eq c qProbe _ .left ha]
  apply config_ext
  · rfl
  · apply Fin.ext
    change k - 1 = k - 1
    rfl
  · funext i
    change (if i = c.head then some ((content x w) ⟨k, hk⟩) else c.tape i) = baseTape B x w i
    by_cases hi : i = c.head
    · rw [if_pos hi]
      subst i
      exact (base_read (B := B) x w hk).symm
    · rw [if_neg hi]
      change erasedTape B x w k i = baseTape B x w i
      apply erased_same x w k i
      intro hv
      apply hi
      apply Fin.ext
      simpa [c, returnConfig] using hv
private theorem run_probe_cycle {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (k : Nat) (hk : k < a + m) (hpos : 0 < k) : machine.run 3 (probeConfig B x w k (Nat.le_of_lt hk)) = probeConfig B x w (k - 1) (by omega) := by
  simp only [UniformTM.run]
  rw [step_probe x w k hk, step_check_pos x w k hk hpos, step_return x w k hk hpos]
private theorem run_rewind {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (r : Nat) (hr : r < a + m) : machine.run (1 + 3 * r) (startConfig B x w) = probeConfig B x w (a + m - 1 - r) (by omega) := by
  induction r with
  | zero =>
      simpa only [Nat.mul_zero, Nat.add_zero, UniformTM.run] using step_start (B := B) x w
  | succ r ih =>
      have hr0 : r < a + m := by omega
      have hk : a + m - 1 - r < a + m := by omega
      have hkpos : 0 < a + m - 1 - r := by omega
      rw [show 1 + 3 * (r + 1) = (1 + 3 * r) + 3 by omega, machine.run_add, ih hr0, run_probe_cycle x w (a + m - 1 - r) hk hkpos]
      congr 1
private theorem step_check_zero {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (hL : 0 < a + m) : machine.stepConfig (checkConfig B x w 0 hL) = if (content x w) ⟨0, hL⟩ then
        tagConfig B x w 1 (by omega) (by omega) (by omega)
      else rejectConfig B x w 0 (by omega) := by
  let c := checkConfig B x w 0 hL
  have hread : c.tape c.head = none := by
    change erasedTape B x w 0
      ⟨0, by unfold tapeLength pairLength; omega⟩ = none
    exact erased_here x w 0 (by unfold tapeLength pairLength; omega)
  by_cases hb : (content x w) ⟨0, hL⟩ = true
  · rw [if_pos hb]
    have ha : machine.step c.state (c.tape c.head) = (qTag ⟨0, by decide⟩, some true, .right) := by
      rw [hread]
      simp [c, checkConfig, hb, machine, UniformTM.step, qCheckT, qAccept, qReject, raw, qTag]
    rw [step_eq c _ _ .right ha]
    apply config_ext
    · rfl
    · apply Fin.ext
      change (moveHead (⟨0, by unfold tapeLength pairLength; omega⟩ : Fin (tapeLength (pairLength a m) B)) .right).1 = 1
      simp [moveHead, show 1 < tapeLength (pairLength a m) B by
        unfold tapeLength pairLength; omega]
    · funext i
      change (if i = c.head then some true else c.tape i) = baseTape B x w i
      by_cases hi : i = c.head
      · rw [if_pos hi]
        subst i
        simpa [hb, c, checkConfig] using (base_read (B := B) x w hL).symm
      · rw [if_neg hi]
        change erasedTape B x w 0 i = baseTape B x w i
        exact erased_same x w 0 i (by
          intro hv
          apply hi
          apply Fin.ext
          simpa [c, checkConfig] using hv)
  · have hb' : (content x w) ⟨0, hL⟩ = false := Bool.eq_false_of_not_eq_true hb
    rw [if_neg hb]
    have ha : machine.step c.state (c.tape c.head) = (qReject, some false, .stay) := by
      rw [hread]
      simp [c, checkConfig, hb', machine, UniformTM.step, qCheckF, qAccept, qReject, raw]
    rw [step_eq c _ _ .stay ha]
    apply config_ext
    · rfl
    · rfl
    · funext i
      change (if i = c.head then some false else c.tape i) = baseTape B x w i
      by_cases hi : i = c.head
      · rw [if_pos hi]
        subst i
        simpa [hb', c, checkConfig] using (base_read (B := B) x w hL).symm
      · rw [if_neg hi]
        change erasedTape B x w 0 i = baseTape B x w i
        exact erased_same x w 0 i (by
          intro hv
          apply hi
          apply Fin.ext
          simpa [c, checkConfig] using hv)
private theorem run_to_first_tag {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (hL : 0 < a + m) : machine.run (3 * (a + m)) (startConfig B x w) = if (content x w) ⟨0, hL⟩ then
        tagConfig B x w 1 (by omega) (by omega) (by omega)
      else rejectConfig B x w 0 (by omega) := by
  rw [show 3 * (a + m) = (1 + 3 * (a + m - 1)) + 2 by omega, machine.run_add, run_rewind x w (a + m - 1) (by omega)]
  have hp : probeConfig B x w (a + m - 1 - (a + m - 1)) (by omega) = probeConfig B x w 0 (by omega) := by
    congr 1
    simp
  rw [hp]
  simp only [UniformTM.run]
  rw [step_probe x w 0 hL, step_check_zero x w hL]
private theorem base_eq_physical {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (j : Nat) (hfit : j < tapeLength (pairLength a m) B) : baseTape B x w ⟨j, hfit⟩ = physicalSymbol (content x w) j := by
  unfold physicalSymbol
  split
  · rename_i hj
    exact base_read x w hj
  · rename_i hj
    exact base_blank x w (Nat.le_of_not_gt hj) hfit
private theorem tag_action_good_next (r : Fin 7) (hr : r.1 < 6) (s : Option Bool)
    (hs : s = some (expectedTagBit ⟨r.1 + 1, by omega⟩)) : machine.step (qTag r) s = (qTag ⟨r.1 + 1, by omega⟩, s, .right) := by
  fin_cases r <;> simp_all [expectedTagBit, machine, UniformTM.step, qTag, qAccept, qReject, raw]
private theorem tag_action_good_last (s : Option Bool)
    (hs : s = some (expectedTagBit ⟨7, by decide⟩)) : machine.step (qTag ⟨6, by decide⟩) s = (qAccept, s, .right) := by
  simp_all [expectedTagBit, machine, UniformTM.step, qTag, qAccept, qReject, raw]
private theorem tag_action_bad (r : Fin 7) (s : Option Bool)
    (hs : s ≠ some (expectedTagBit ⟨r.1 + 1, by omega⟩)) : machine.step (qTag r) s = (qReject, s, .stay) := by
  fin_cases r <;> cases s <;> simp_all [expectedTagBit, machine, UniformTM.step, qTag, qAccept, qReject, raw]
private theorem step_tag_good_next {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (j : Nat) (hj1 : 1 ≤ j) (hj6 : j ≤ 6) (hjL : j ≤ a + m)
    (hgood : physicalSymbol (content x w) j = some (expectedTagBit ⟨j, by omega⟩)) : machine.stepConfig (tagConfig B x w j hj1 (by omega) hjL) = tagConfig B x w (j + 1) (by omega) (by omega) (by
        have hlt := physical_present_lt _ _ _ hgood
        omega) := by
  let c := tagConfig B x w j hj1 (by omega) hjL
  have hread : c.tape c.head = some (expectedTagBit ⟨j, by omega⟩) := by
    change baseTape B x w ⟨j, by unfold tapeLength pairLength; omega⟩ = _
    rw [base_eq_physical x w j (by unfold tapeLength pairLength; omega)]
    exact hgood
  have ha : machine.step c.state (c.tape c.head) = (qTag ⟨j, by omega⟩, c.tape c.head, .right) := by
    have hs : c.tape c.head = some (expectedTagBit ⟨(j - 1) + 1, by omega⟩) := by
      simpa only [show j - 1 + 1 = j by omega] using hread
    let r : Fin 7 := ⟨j - 1, by omega⟩
    have hr : r.1 < 6 := by dsimp [r]; omega
    have hh := tag_action_good_next r hr (c.tape c.head) (by
      simpa only [r] using hs)
    simpa only [c, tagConfig, r, show j - 1 + 1 = j by omega] using hh
  rw [step_keep c _ .right ha]
  apply config_ext
  · rfl
  · apply Fin.ext
    have hlt := physical_present_lt _ _ _ hgood
    simp [c, tagConfig, moveHead, show j + 1 < tapeLength (pairLength a m) B by
      unfold tapeLength pairLength; omega]
  · rfl
private theorem step_tag_good_last {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (h7L : 7 ≤ a + m)
    (hgood : physicalSymbol (content x w) 7 = some (expectedTagBit ⟨7, by decide⟩)) : machine.stepConfig (tagConfig B x w 7 (by omega) (by omega) h7L) = acceptConfig B x w (by
        have hlt := physical_present_lt _ _ _ hgood
        omega) := by
  let c := tagConfig B x w 7 (by omega) (by omega) h7L
  have hread : c.tape c.head = some (expectedTagBit ⟨7, by decide⟩) := by
    change baseTape B x w ⟨7, by unfold tapeLength pairLength; omega⟩ = _
    rw [base_eq_physical x w 7 (by unfold tapeLength pairLength; omega)]
    exact hgood
  have ha : machine.step c.state (c.tape c.head) = (qAccept, c.tape c.head, .right) := by
    apply tag_action_good_last
    exact hread
  rw [step_keep c _ .right ha]
  apply config_ext
  · rfl
  · apply Fin.ext
    have hlt := physical_present_lt _ _ _ hgood
    change (moveHead (⟨7, by unfold tapeLength pairLength; omega⟩ : Fin (tapeLength (pairLength a m) B)) .right).1 = 8
    simp [moveHead, show 8 < tapeLength (pairLength a m) B by
      unfold tapeLength pairLength; omega]
  · rfl
private theorem step_tag_bad {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (j : Nat) (hj1 : 1 ≤ j) (hj7 : j ≤ 7) (hjL : j ≤ a + m)
    (hbad : physicalSymbol (content x w) j ≠
      some (expectedTagBit ⟨j, by omega⟩)) : machine.stepConfig (tagConfig B x w j hj1 hj7 hjL) = rejectConfig B x w j hjL := by
  let c := tagConfig B x w j hj1 hj7 hjL
  have hread : c.tape c.head = physicalSymbol (content x w) j := by
      change baseTape B x w ⟨j, by unfold tapeLength pairLength; omega⟩ = _
      exact base_eq_physical x w j (by unfold tapeLength pairLength; omega)
  have ha : machine.step c.state (c.tape c.head) = (qReject, c.tape c.head, .stay) := by
    have hs : c.tape c.head ≠
        some (expectedTagBit ⟨(j - 1) + 1, by omega⟩) := by
      rw [hread]
      simpa only [show j - 1 + 1 = j by omega] using hbad
    have hh := tag_action_bad ⟨j - 1, by omega⟩ (c.tape c.head) hs
    simpa only [c, tagConfig] using hh
  rw [step_keep c qReject .stay ha]
  apply config_ext
  · rfl
  · rfl
  · rfl
private theorem run_tag_prefix {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (h1L : 1 ≤ a + m) (r : Nat) (hr6 : r ≤ 6) (hrL : r + 1 ≤ a + m)
    (hpre : ∀ i : Fin 8, 1 ≤ i.1 → i.1 < r + 1 → physicalSymbol (content x w) i.1 = some (expectedTagBit i)) : machine.run r (tagConfig B x w 1 (by omega) (by omega) h1L) = tagConfig B x w (r + 1) (by omega) (by omega) hrL := by
  induction r with
  | zero => rfl
  | succ r ih =>
      have hr6' : r ≤ 6 := by omega
      let i : Fin 8 := ⟨r + 1, by omega⟩
      have hgood := hpre i (by dsimp [i]; omega) (by dsimp [i]; omega)
      have hrL' : r + 1 ≤ a + m := by
        exact Nat.le_of_lt (physical_present_lt _ _ _ hgood)
      rw [machine.run_add r 1, ih hr6' hrL' (fun i hi1 hir => hpre i hi1 (by omega))]
      exact step_tag_good_next x w (r + 1) (by omega) (by omega) hrL' hgood
private theorem run_empty {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (hL : a + m = 0) : machine.run 2 (startConfig B x w) = rejectConfig B x w 0 (by omega) := by
  have hs := step_start (B := B) x w
  have hp : probeConfig B x w (a + m - 1) (by omega) = probeConfig B x w 0 (by omega) := by
    apply config_ext <;> simp [hL, probeConfig]
  change machine.stepConfig (machine.stepConfig (startConfig B x w)) = _
  rw [hs, hp]
  let c := probeConfig B x w 0 (by omega)
  have hread : c.tape c.head = none := by
    exact base_blank x w (by omega) (by unfold tapeLength pairLength; omega)
  have ha : machine.step c.state (c.tape c.head) = (qReject, c.tape c.head, .stay) := by
    rw [hread]
    rfl
  rw [step_keep c qReject .stay ha]
  apply config_ext <;> rfl
private theorem run_bad {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (hL : 0 < a + m) (j : Nat) (hj7 : j ≤ 7) (hjL : j ≤ a + m)
    (hpre : ∀ i : Fin 8, i.1 < j → physicalSymbol (content x w) i.1 = some (expectedTagBit i))
    (hbad : physicalSymbol (content x w) j ≠
      some (expectedTagBit ⟨j, by omega⟩)) : machine.run (3 * (a + m) + j) (startConfig B x w) = rejectConfig B x w j hjL := by
  by_cases hj0 : j = 0
  · subst j
    have hb : (content x w) ⟨0, hL⟩ = false := by
      cases hc : (content x w) ⟨0, hL⟩ <;>
        simp_all [physicalSymbol, expectedTagBit]
    simpa [hb] using run_to_first_tag (B := B) x w hL
  · have hj1 : 1 ≤ j := by omega
    have hz : (0 : Nat) < j := by omega
    have hzero := hpre ⟨0, by decide⟩ hz
    have hb : (content x w) ⟨0, hL⟩ = true := by
      simpa [physicalSymbol, expectedTagBit, hL] using hzero
    rw [show 3 * (a + m) + j = 3 * (a + m) + (j - 1) + 1 by omega, machine.run_add, machine.run_add, run_to_first_tag x w hL, if_pos hb, run_tag_prefix x w (by omega) (j - 1) (by omega) (by omega)
        (fun i hi1 hij => hpre i (by omega))]
    simpa only [show j - 1 + 1 = j by omega] using
      step_tag_bad x w j hj1 hj7 hjL hbad
private theorem run_good {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (h : ∀ i : Fin 8, physicalSymbol (content x w) i.1 = some (expectedTagBit i)) : machine.run (deadline a m) (startConfig B x w) = acceptConfig B x w (by
        have h7 := physical_present_lt _ _ _ (h ⟨7, by decide⟩)
        change 7 < a + m at h7
        omega) := by
  have hL : 0 < a + m := by
    have h0 := physical_present_lt _ _ _ (h ⟨0, by decide⟩)
    omega
  have hb : (content x w) ⟨0, hL⟩ = true := by
    simpa [physicalSymbol, expectedTagBit, hL] using h ⟨0, by decide⟩
  have h7L : 7 ≤ a + m := by
    have h7' := physical_present_lt _ _ _ (h ⟨7, by decide⟩)
    change 7 < a + m at h7'
    omega
  rw [show deadline a m = 3 * (a + m) + 6 + 1 by rfl, machine.run_add, machine.run_add, run_to_first_tag x w hL, if_pos hb, run_tag_prefix x w (by omega) 6 (by omega) h7L
      (fun i _ _ => h i)]
  exact step_tag_good_last x w h7L (h ⟨7, by decide⟩)
private theorem reject_absorbs_to_deadline {a m B : Nat}
    (x : Bitstring a) (w : Bitstring m) (j : Nat) (hj7 : j ≤ 7)
    (hjL : j ≤ a + m)
    (hbadRun : machine.run (3 * (a + m) + j) (startConfig B x w) = rejectConfig B x w j hjL) : machine.run (deadline a m) (startConfig B x w) = rejectConfig B x w j hjL := by
  rw [show deadline a m = (3 * (a + m) + j) + (7 - j) by
    unfold deadline; omega, machine.run_add, hbadRun, machine.run_reject (rejectConfig B x w j hjL) rfl]
private theorem run_deadline_bad {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (hL : 0 < a + m) (j : Nat) (hj7 : j ≤ 7) (hjL : j ≤ a + m)
    (hpre : ∀ i : Fin 8, i.1 < j → physicalSymbol (content x w) i.1 = some (expectedTagBit i))
    (hbad : physicalSymbol (content x w) j ≠
      some (expectedTagBit ⟨j, by omega⟩))
    (hidx : badIndex (content x w) = j) : machine.run (deadline a m) (startConfig B x w) = finalConfig B x w := by
  have hr := run_bad (B := B) x w hL j hj7 hjL hpre hbad
  rw [reject_absorbs_to_deadline x w j hj7 hjL hr]
  have hidx' : badIndex (Fin.append x w) = j := by simpa only [content] using hidx
  have htag : tagMatches (Fin.append x w) = false := by
    simp [tagMatches, hidx', show j ≠ 8 by omega]
  apply config_ext
  · change qReject = (if tagMatches (Fin.append x w) then qAccept else qReject)
    simp [htag]
  · apply Fin.ext
    change j = min (badIndex (Fin.append x w)) (a + m)
    rw [hidx', Nat.min_eq_left hjL]
  · rfl
theorem handoff_exact {a m B : Nat} (x : Bitstring a) (w : Bitstring m) : let p := FixedPairContentMarkerErase.machine.run (FixedPairContentMarkerErase.clock a m) (FixedPairContentMarkerErase.startConfig B x w)
    p = FixedPairContentMarkerErase.finalConfig B x w ∧ p.state = FixedPairContentMarkerErase.qAccept ∧ (startConfig B x w).state = machine.start ∧ (startConfig B x w).head = p.head ∧ (startConfig B x w).tape = p.tape := by
  dsimp
  rw [FixedPairContentMarkerErase.run_exact]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem run_deadline {a m B : Nat} (x : Bitstring a) (w : Bitstring m) : machine.run (deadline a m) (startConfig B x w) = finalConfig B x w := by
  by_cases hL : a + m = 0
  · have hr := run_empty (B := B) x w hL
    rw [show deadline a m = 2 + 5 by simp [deadline, hL], machine.run_add, hr, machine.run_reject (rejectConfig B x w 0 (by omega)) rfl]
    apply config_ext
    · change qReject = (if tagMatches (Fin.append x w) then qAccept else qReject)
      simp [tagMatches, badIndex, physicalSymbol, hL]
    · apply Fin.ext
      change 0 = min (badIndex (Fin.append x w)) (a + m)
      simp [badIndex, physicalSymbol, hL]
    · rfl
  · have hpos : 0 < a + m := Nat.pos_of_ne_zero hL
    let b := badIndex (content x w)
    by_cases hb8 : b = 8
    · have hall : ∀ i : Fin 8, physicalSymbol (content x w) i.1 = some (expectedTagBit i) := (badIndex_eq_eight_iff _).1 hb8
      rw [run_good x w hall]
      have hidx' : badIndex (Fin.append x w) = 8 := by simpa only [content] using hb8
      have htag : tagMatches (Fin.append x w) = true := by simp [tagMatches, hidx']
      apply config_ext
      · change qAccept = (if tagMatches (Fin.append x w) then qAccept else qReject)
        simp [htag]
      · apply Fin.ext
        have h7 := physical_present_lt _ _ _ (hall ⟨7, by decide⟩)
        change 7 < a + m at h7
        change 8 = min (badIndex (Fin.append x w)) (a + m)
        rw [hidx', Nat.min_eq_left (by omega)]
      · rfl
    · have hb : b < 8 := by have := badIndex_le_eight (content x w); omega
      have hs := badIndex_lt_specs (content x w) hb
      have hbL : b ≤ a + m := badIndex_le_length (content x w) hpos
      exact run_deadline_bad x w hpos b (by omega) hbL hs.2 hs.1 (by rfl)
private theorem rewind_no_terminal {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (hL : 0 < a + m) (s : Nat) (hs : s < 3 * (a + m)) : (machine.run s (startConfig B x w)).state ≠ qAccept ∧ (machine.run s (startConfig B x w)).state ≠ qReject := by
  by_cases hs0 : s = 0
  · subst s
    change qStart ≠ qAccept ∧ qStart ≠ qReject
    decide
  · let r := (s - 1) / 3
    let d := (s - 1) % 3
    have hd : d < 3 := Nat.mod_lt _ (by decide)
    have hmul : r * 3 ≤ s - 1 := by
      exact Nat.div_mul_le_self (s - 1) 3
    have hr : r < a + m := by
      dsimp [r] at hmul ⊢
      omega
    have hdecomp : s = (1 + 3 * r) + d := by
      have hmod := Nat.mod_add_div (s - 1) 3
      dsimp [r, d]
      omega
    rw [hdecomp, machine.run_add, run_rewind x w r hr]
    rcases Nat.eq_zero_or_pos d with hd0 | hdpos
    · rw [hd0]
      change qProbe ≠ qAccept ∧ qProbe ≠ qReject
      decide
    · by_cases hd1 : d = 1
      · rw [hd1]
        simp only [UniformTM.run]
        rw [step_probe x w (a + m - 1 - r) (by omega)]
        change (if (content x w) ⟨a + m - 1 - r, _⟩ then qCheckT else qCheckF) ≠
            qAccept ∧ (if (content x w) ⟨a + m - 1 - r, _⟩ then qCheckT else qCheckF) ≠
            qReject
        split <;> decide
      · have hd2 : d = 2 := by omega
        have hkpos : 0 < a + m - 1 - r := by
          by_contra hk
          have : s = 3 * (a + m) := by
            dsimp [r] at hk
            omega
          omega
        rw [hd2]
        simp only [UniformTM.run]
        rw [step_probe x w (a + m - 1 - r) (by omega), step_check_pos x w (a + m - 1 - r) (by omega) hkpos]
        change (if (content x w) ⟨a + m - 1 - r, _⟩ then qReturnT else qReturnF) ≠
            qAccept ∧ (if (content x w) ⟨a + m - 1 - r, _⟩ then qReturnT else qReturnF) ≠
            qReject
        split <;> decide
private theorem no_terminal_before_index {a m B : Nat}
    (x : Bitstring a) (w : Bitstring m) (hL : 0 < a + m)
    (j : Nat) (hj7 : j ≤ 7)
    (hpre : ∀ i : Fin 8, i.1 < j → physicalSymbol (content x w) i.1 = some (expectedTagBit i))
    (s : Nat) (hs : s < 3 * (a + m) + j) : (machine.run s (startConfig B x w)).state ≠ qAccept ∧ (machine.run s (startConfig B x w)).state ≠ qReject := by
  by_cases hrewind : s < 3 * (a + m)
  · exact rewind_no_terminal x w hL s hrewind
  · let t := s - 3 * (a + m)
    have ht : t < j := by dsimp [t]; omega
    have hsdecomp : s = 3 * (a + m) + t := by dsimp [t]; omega
    have hjpos : 0 < j := by omega
    have hzero := hpre ⟨0, by decide⟩ (by omega)
    have hb : (content x w) ⟨0, hL⟩ = true := by
      simpa [physicalSymbol, expectedTagBit, hL] using hzero
    have htL : t + 1 ≤ a + m := by
      have hp := hpre ⟨t, by omega⟩ ht
      exact physical_present_lt _ _ _ hp
    rw [hsdecomp, machine.run_add, run_to_first_tag x w hL, if_pos hb, run_tag_prefix x w (by omega) t (by omega) htL
        (fun i hi1 hit => hpre i (by omega))]
    change qTag ⟨t, by omega⟩ ≠ qAccept ∧ qTag ⟨t, by omega⟩ ≠ qReject
    constructor <;> intro h
    all_goals have hv := congrArg Fin.val h
    all_goals simp [qTag, qAccept, qReject] at hv
    all_goals omega
theorem exact_terminal_contract {a m B : Nat} (x : Bitstring a) (w : Bitstring m) : (a + m = 0 → (∀ s < 2, (machine.run s (startConfig B x w)).state ≠ machine.accept ∧ (machine.run s (startConfig B x w)).state ≠ machine.reject) ∧ machine.run 2 (startConfig B x w) = rejectConfig B x w 0 (by omega)) ∧ (∀ (j : Nat), (hpos : 0 < a + m) → (hj7 : j ≤ 7) → (hjL : j ≤ a + m) → (∀ i : Fin 8, i.1 < j → physicalSymbol (content x w) i.1 = some (expectedTagBit i)) → physicalSymbol (content x w) j ≠ some (expectedTagBit ⟨j, by omega⟩) → (∀ s < 3 * (a + m) + j, (machine.run s (startConfig B x w)).state ≠ machine.accept ∧ (machine.run s (startConfig B x w)).state ≠ machine.reject) ∧ machine.run (3 * (a + m) + j) (startConfig B x w) = rejectConfig B x w j hjL) ∧ ((hpos : 0 < a + m) → (hshort : a + m < 8) → (∀ i : Fin 8, i.1 < a + m → physicalSymbol (content x w) i.1 = some (expectedTagBit i)) → (∀ s < 4 * (a + m), (machine.run s (startConfig B x w)).state ≠ machine.accept ∧ (machine.run s (startConfig B x w)).state ≠ machine.reject) ∧ (machine.run (4 * (a + m)) (startConfig B x w)).state = machine.reject ∧ (machine.run (4 * (a + m)) (startConfig B x w)).head.1 = a + m ∧ (machine.run (4 * (a + m)) (startConfig B x w)).tape = baseTape B x w) ∧ (∀ h : (∀ i : Fin 8, physicalSymbol (content x w) i.1 = some (expectedTagBit i)), (∀ s < deadline a m, (machine.run s (startConfig B x w)).state ≠ machine.accept ∧ (machine.run s (startConfig B x w)).state ≠ machine.reject) ∧ machine.run (deadline a m) (startConfig B x w) = acceptConfig B x w (by
          have h7 := physical_present_lt _ _ _ (h ⟨7, by decide⟩)
          change 7 < a + m at h7
          omega)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hzero
    refine ⟨?_, run_empty x w hzero⟩
    intro s hs
    interval_cases s
    · change qStart ≠ qAccept ∧ qStart ≠ qReject
      decide
    · rw [show machine.run 1 (startConfig B x w) = probeConfig B x w 0 (by omega) by
        simpa [hzero] using step_start (B := B) x w]
      change qProbe ≠ qAccept ∧ qProbe ≠ qReject
      decide
  · intro j hpos hj7 hjL hpre hbad
    exact ⟨fun s hs => no_terminal_before_index x w hpos j hj7 hpre s hs, run_bad x w hpos j hj7 hjL hpre hbad⟩
  · intro hpos hshort hpre
    have hbad : physicalSymbol (content x w) (a + m) ≠
        some (expectedTagBit ⟨a + m, hshort⟩) := by simp [physicalSymbol]
    have hr := run_bad (B := B) x w hpos (a + m) (by omega) (le_refl _) hpre hbad
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro s hs
      apply no_terminal_before_index x w hpos (a + m) (by omega) hpre s
      omega
    · simpa [show 3 * (a + m) + (a + m) = 4 * (a + m) by omega] using
        congrArg Config.state hr
    · simpa [show 3 * (a + m) + (a + m) = 4 * (a + m) by omega] using
        congrArg (fun c => c.head.1) hr
    · simpa [show 3 * (a + m) + (a + m) = 4 * (a + m) by omega] using
        congrArg Config.tape hr
  · intro h
    refine ⟨fun s hs => no_terminal_before_index x w (by
        have h0 := physical_present_lt _ _ _ (h ⟨0, by decide⟩)
        omega) 7 (by omega) (fun i _ => h i) s (by simpa [deadline] using hs), run_good x w h⟩
private inductive TraceShape {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (s : Nat) : Prop where
  | start (hs : s = 0) (hrun : ∀ B, machine.run s (startConfig B x w) = startConfig B x w)
  | emptyProbe (hL : a + m = 0) (hs : s = 1)
      (hrun : ∀ B, machine.run s (startConfig B x w) = probeConfig B x w 0 (by omega))
  | probe (hL : 0 < a + m) (r : Nat) (hr : r < a + m)
      (hs : s = 1 + 3 * r)
      (hrun : ∀ B, machine.run s (startConfig B x w) = probeConfig B x w (a + m - 1 - r) (by omega))
  | check (hL : 0 < a + m) (r : Nat) (hr : r < a + m)
      (hs : s = 2 + 3 * r)
      (hrun : ∀ B, machine.run s (startConfig B x w) = checkConfig B x w (a + m - 1 - r) (by omega))
  | ret (hL : 0 < a + m) (r : Nat) (hr : r + 1 < a + m)
      (hs : s = 3 + 3 * r)
      (hrun : ∀ B, machine.run s (startConfig B x w) = returnConfig B x w (a + m - 1 - r) (by omega))
  | tag (hL : 0 < a + m) (t : Nat) (ht : t ≤ 6)
      (hfit : t + 1 ≤ a + m) (hs : s = 3 * (a + m) + t)
      (hpre : ∀ i : Fin 8, i.1 < t + 1 → physicalSymbol (content x w) i.1 = some (expectedTagBit i))
      (hrun : ∀ B, machine.run s (startConfig B x w) = tagConfig B x w (t + 1) (by omega) (by omega) hfit)
  | rejected (j : Nat) (hj : j ≤ a + m)
      (htime : (if a + m = 0 then 2 else 3 * (a + m)) ≤ s)
      (hs : ∀ B, machine.run s (startConfig B x w) = rejectConfig B x w j hj)
  | accepted (h8 : 8 ≤ a + m)
      (htime : s = deadline a m)
      (hs : ∀ B, machine.run s (startConfig B x w) = acceptConfig B x w h8)
private theorem run_shape {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (s : Nat) (hsD : s ≤ deadline a m) : TraceShape x w s := by
  by_cases hzero : a + m = 0
  · by_cases hs0 : s = 0
    · exact .start hs0 (fun B => by subst s; rfl)
    · by_cases hs1 : s = 1
      · apply TraceShape.emptyProbe hzero hs1
        intro B
        subst s
        simpa [hzero] using step_start (B := B) x w
      · apply TraceShape.rejected 0 (by omega) (by simp [hzero]; omega)
        intro B
        rw [show s = 2 + (s - 2) by omega, machine.run_add, run_empty x w hzero, machine.run_reject (rejectConfig B x w 0 (by omega)) rfl]
  · have hL : 0 < a + m := Nat.pos_of_ne_zero hzero
    by_cases hrewind : s < 3 * (a + m)
    · by_cases hs0 : s = 0
      · exact .start hs0 (fun B => by subst s; rfl)
      · let r := (s - 1) / 3
        let d := (s - 1) % 3
        have hd : d < 3 := Nat.mod_lt _ (by decide)
        have hmul : r * 3 ≤ s - 1 := Nat.div_mul_le_self _ _
        have hr : r < a + m := by dsimp [r] at hmul ⊢; omega
        have heq : s = 1 + 3 * r + d := by
          have hm := Nat.mod_add_div (s - 1) 3
          dsimp [r, d]
          omega
        rcases Nat.eq_zero_or_pos d with hd0 | hdpos
        · apply TraceShape.probe hL r hr (by omega)
          intro B
          simpa [heq, hd0] using run_rewind (B := B) x w r hr
        · by_cases hd1 : d = 1
          · apply TraceShape.check hL r hr (by omega)
            intro B
            have htime : s = (1 + 3 * r) + 1 := by omega
            refine (congrArg (fun u => machine.run u (startConfig B x w)) htime).trans ?_
            rw [machine.run_add, run_rewind x w r hr]
            simpa only [UniformTM.run] using
              step_probe (B := B) x w (a + m - 1 - r) (by omega)
          · have hd2 : d = 2 := by omega
            have hr' : r + 1 < a + m := by
              by_contra hn
              dsimp [r] at hn
              omega
            apply TraceShape.ret hL r hr' (by omega)
            intro B
            have htime : s = (1 + 3 * r) + 2 := by omega
            refine (congrArg (fun u => machine.run u (startConfig B x w)) htime).trans ?_
            rw [machine.run_add, run_rewind x w r hr]
            simp only [UniformTM.run]
            rw [step_probe x w (a + m - 1 - r) (by omega), step_check_pos x w (a + m - 1 - r) (by omega) (by omega)]
    · let b := badIndex (content x w)
      have hbL : b ≤ a + m := badIndex_le_length _ hL
      by_cases hb8 : b = 8
      · have hall := (badIndex_eq_eight_iff _).1 hb8
        by_cases hterm : s = deadline a m
        · apply TraceShape.accepted (by
            have h7 := physical_present_lt _ _ _ (hall ⟨7, by decide⟩)
            change 7 < a + m at h7
            omega) hterm
          intro B
          simpa [hterm] using run_good (B := B) x w hall
        · let t := s - 3 * (a + m)
          have ht : t ≤ 6 := by dsimp [t]; unfold deadline at hsD hterm; omega
          have hs : s = 3 * (a + m) + t := by dsimp [t]; omega
          have hfit : t + 1 ≤ a + m := by
            have hp := physical_present_lt _ _ _ (hall ⟨t, by omega⟩)
            exact hp
          apply TraceShape.tag hL t ht hfit hs (fun i _ => hall i)
          intro B
          have hb : (content x w) ⟨0, hL⟩ = true := by
            simpa [physicalSymbol, expectedTagBit, hL] using hall ⟨0, by decide⟩
          refine (congrArg (fun u => machine.run u (startConfig B x w)) hs).trans ?_
          rw [machine.run_add, run_to_first_tag x w hL, if_pos hb, run_tag_prefix x w (by omega) t ht hfit (fun i _ hi => hall i)]
      · have hb : b < 8 := by
          have := badIndex_le_eight (content x w)
          omega
        have hspec := badIndex_lt_specs (content x w) hb
        by_cases hbefore : s < 3 * (a + m) + b
        · let t := s - 3 * (a + m)
          have ht : t < b := by dsimp [t]; omega
          have hs : s = 3 * (a + m) + t := by dsimp [t]; omega
          have hfit : t + 1 ≤ a + m := by
            have hp := hspec.2 ⟨t, by omega⟩ ht
            exact physical_present_lt _ _ _ hp
          have hpre : ∀ i : Fin 8, i.1 < t + 1 → physicalSymbol (content x w) i.1 = some (expectedTagBit i) := fun i hi => hspec.2 i (by omega)
          apply TraceShape.tag hL t (by omega) hfit hs hpre
          intro B
          have hb0 : (content x w) ⟨0, hL⟩ = true := by
            have hz : physicalSymbol (content x w) 0 = some (expectedTagBit ⟨0, by decide⟩) := hpre ⟨0, by decide⟩ (by
              change (0 : Nat) < t + 1
              omega)
            simpa [physicalSymbol, expectedTagBit, hL] using hz
          refine (congrArg (fun u => machine.run u (startConfig B x w)) hs).trans ?_
          rw [machine.run_add, run_to_first_tag x w hL, if_pos hb0, run_tag_prefix x w (by omega) t (by omega) hfit
              (fun i hi1 hi => hpre i (by omega))]
        · apply TraceShape.rejected b hbL (by rw [if_neg hzero]; omega)
          intro B
          have hr := run_bad (B := B) x w hL b (by omega) hbL hspec.2 hspec.1
          rw [show s = (3 * (a + m) + b) + (s - (3 * (a + m) + b)) by omega, machine.run_add, hr, machine.run_reject (rejectConfig B x w b hbL) rfl]
private theorem start_move {a m B : Nat} (x : Bitstring a) (w : Bitstring m) : (machine.step (startConfig B x w).state
      ((startConfig B x w).tape (startConfig B x w).head)).2.2 = .left := by
  have hread : (startConfig B x w).tape (startConfig B x w).head = none := base_blank x w (le_refl _) (by unfold tapeLength pairLength; omega)
  rw [hread]
  rfl
private theorem probe_move {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (k : Nat) (hk : k ≤ a + m) : (machine.step (probeConfig B x w k hk).state
      ((probeConfig B x w k hk).tape (probeConfig B x w k hk).head)).2.2 = if k < a + m then .left else .stay := by
  by_cases hlt : k < a + m
  · rw [if_pos hlt]
    change (machine.step qProbe
      (baseTape B x w ⟨k, by unfold tapeLength pairLength; omega⟩)).2.2 = .left
    rw [base_read x w hlt]
    cases (content x w) ⟨k, hlt⟩ <;> rfl
  · rw [if_neg hlt]
    change (machine.step qProbe
      (baseTape B x w ⟨k, by unfold tapeLength pairLength; omega⟩)).2.2 = .stay
    rw [base_blank x w (by omega) (by unfold tapeLength pairLength; omega)]
    rfl
private theorem check_not_left {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (k : Nat) (hk : k < a + m) : (machine.step (checkConfig B x w k hk).state
      ((checkConfig B x w k hk).tape (checkConfig B x w k hk).head)).2.2 ≠ .left := by
  cases hb : (content x w) ⟨k, hk⟩ <;>
    cases hs : (checkConfig B x w k hk).tape (checkConfig B x w k hk).head <;>
      simp [checkConfig, hb, machine, UniformTM.step, qCheckF, qCheckT, qAccept, qReject, raw]
private theorem return_move {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (k : Nat) (hk : k < a + m) : (machine.step (returnConfig B x w k hk).state
      ((returnConfig B x w k hk).tape (returnConfig B x w k hk).head)).2.2 = .left := by
  have hread := erased_here (B := B) x w k (by unfold tapeLength pairLength; omega)
  cases hb : (content x w) ⟨k, hk⟩ <;>
    simp [returnConfig, hb, hread, machine, UniformTM.step, qReturnF, qReturnT, qAccept, qReject, raw]
private theorem tag_not_left {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (j : Nat) (hj1 : 1 ≤ j) (hj7 : j ≤ 7) (hjL : j ≤ a + m) : let c := tagConfig B x w j hj1 hj7 hjL
    (machine.step c.state (c.tape c.head)).2.2 ≠ .left := by
  dsimp
  cases hs : baseTape B x w
      ⟨j, by unfold tapeLength pairLength; omega⟩ with
  | none => interval_cases j <;>
      simp [tagConfig, machine, UniformTM.step, qTag, qAccept, qReject, raw, hs]
  | some b => cases b <;> interval_cases j <;>
      simp [tagConfig, machine, UniformTM.step, qTag, qAccept, qReject, raw, hs]
private theorem baseTape_independent {a m B B' : Nat}
    (x : Bitstring a) (w : Bitstring m)
    (i : Fin (tapeLength (pairLength a m) B))
    (i' : Fin (tapeLength (pairLength a m) B')) (hii : i.1 = i'.1) : baseTape B x w i = baseTape B' x w i' := by
  simp [baseTape, FixedPairContentMarkerErase.contentTape, hii]
private theorem erasedTape_independent {a m B B' : Nat}
    (x : Bitstring a) (w : Bitstring m) (k : Nat)
    (i : Fin (tapeLength (pairLength a m) B))
    (i' : Fin (tapeLength (pairLength a m) B')) (hii : i.1 = i'.1) : erasedTape B x w k i = erasedTape B' x w k i' := by
  simp [erasedTape, hii, baseTape_independent x w i i' hii]
theorem phase_contract {a m : Nat} (x : Bitstring a) (w : Bitstring m) : (∀ B s, s ≤ deadline a m → (machine.run s (startConfig B x w)).head.1 ≤ a + m) ∧ (∀ B s, s < deadline a m → let c := machine.run s (startConfig B x w)
      (machine.step c.state (c.tape c.head)).2.2 = .right → c.head.1 + 1 < tapeLength (pairLength a m) B) ∧ (∀ B s, s < deadline a m → let c := machine.run s (startConfig B x w)
      ((machine.step c.state (c.tape c.head)).2.2 = .left ∧ c.head.1 = 0 ↔
        s = if a + m = 0 then 0 else 3 * (a + m) - 2)) ∧ (∀ B, (machine.run (deadline a m) (startConfig B x w)).tape = FixedPairContentMarkerErase.contentTape B x w) ∧ (∀ B (i : Fin (tapeLength (pairLength a m) B)), a + m ≤ i.1 → (machine.run (deadline a m) (startConfig B x w)).tape i = none) ∧ (∀ B extra, machine.run (deadline a m + extra) (startConfig B x w) = finalConfig B x w) ∧ (∀ B B' s, s ≤ deadline a m → let c := machine.run s (startConfig B x w)
      let c' := machine.run s (startConfig B' x w)
      c.state = c'.state ∧ c.head.1 = c'.head.1 ∧ ∀ (i : Fin (tapeLength (pairLength a m) B))
        (i' : Fin (tapeLength (pairLength a m) B')), i.1 = i'.1 → c.tape i = c'.tape i') := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro B s hs
    cases run_shape x w s hs with
    | start _ hrun => rw [hrun B]; rfl
    | emptyProbe hL _ hrun => rw [hrun B]; simp [probeConfig]
    | probe _ r hr _ hrun => rw [hrun B]; simp [probeConfig]; omega
    | check _ r hr _ hrun => rw [hrun B]; simp [checkConfig]; omega
    | ret _ r hr _ hrun => rw [hrun B]; simp [returnConfig]; omega
    | tag _ t _ hfit _ _ hrun => rw [hrun B]; simpa [tagConfig] using hfit
    | rejected j hj _ hrun => rw [hrun B]; simpa [rejectConfig] using hj
    | accepted h8 _ hrun => rw [hrun B]; simpa [acceptConfig] using h8
  · intro B s hs
    dsimp
    intro hright
    have hhead := (run_shape x w s (Nat.le_of_lt hs))
    cases hhead with
    | start _ hrun => rw [hrun B, start_move x w] at hright; contradiction
    | emptyProbe hL _ hrun =>
        rw [hrun B, probe_move x w 0 (by omega), if_neg (by omega)] at hright
        contradiction
    | probe hL r hr _ hrun =>
        rw [hrun B, probe_move x w _ (by omega), if_pos (by omega)] at hright
        contradiction
    | check hL r hr _ hrun =>
        rw [hrun B]
        simp only [checkConfig]
        unfold tapeLength pairLength
        omega
    | ret hL r hr _ hrun => rw [hrun B, return_move x w _ _] at hright; contradiction
    | tag hL t ht hfit _ _ hrun =>
        rw [hrun B] at hright ⊢
        by_cases hp : t + 1 < a + m
        · simp only [tagConfig]
          unfold tapeLength pairLength
          omega
        · have heq : t + 1 = a + m := by omega
          have hblank := base_blank (B := B) x w (le_of_eq heq.symm)
            (by unfold tapeLength pairLength; omega)
          change (machine.step (qTag ⟨t, by omega⟩)
            (baseTape B x w ⟨t + 1, by unfold tapeLength pairLength; omega⟩)).2.2 = .right at hright
          rw [hblank] at hright
          interval_cases t <;>
            simp [machine, UniformTM.step, qTag, qAccept, qReject, raw] at hright
    | rejected j hj _ hrun =>
        rw [hrun B] at hright
        simp [rejectConfig, machine, UniformTM.step, qReject] at hright
    | accepted h8 _ hrun =>
        rw [hrun B] at hright
        simp [acceptConfig, machine, UniformTM.step, qAccept] at hright
  · intro B s hs
    dsimp
    cases sh : run_shape x w s (Nat.le_of_lt hs) with
    | start hs0 hrun =>
        rw [hrun B, start_move x w]
        subst s
        by_cases hz : a + m = 0
        · simp [startConfig, FixedPairContentMarkerErase.finalConfig, hz]
        · rw [if_neg hz]
          simp [startConfig, FixedPairContentMarkerErase.finalConfig]
          omega
    | emptyProbe hL hs1 hrun =>
        rw [hrun B, probe_move x w 0 (by omega), if_neg (by omega)]
        subst s
        simp [hL]
    | probe hL r hr hsrun hrun =>
        rw [hrun B, probe_move x w _ (by omega), if_pos (by omega)]
        subst s
        rw [if_neg (by omega : a + m ≠ 0)]
        simp [probeConfig]
        omega
    | check hL r hr hsrun hrun =>
        rw [hrun B]
        subst s
        rw [if_neg (by omega : a + m ≠ 0)]
        constructor
        · intro hc
          exact False.elim
            ((check_not_left (B := B) x w (a + m - 1 - r) (by omega)) hc.1)
        · intro heq
          omega
    | ret hL r hr hsrun hrun =>
        rw [hrun B, return_move x w _ _]
        subst s
        rw [if_neg (by omega : a + m ≠ 0)]
        simp [returnConfig]
        omega
    | tag hL t ht hfit hsrun hpre hrun =>
        rw [hrun B]
        subst s
        rw [if_neg (by omega : a + m ≠ 0)]
        constructor
        · intro hc
          exact False.elim
            ((tag_not_left (B := B) x w (t + 1) (by omega) (by omega) hfit) hc.1)
        · intro heq
          omega
    | rejected j hj htime hrun =>
        have hne : s ≠ (if a + m = 0 then 0 else 3 * (a + m) - 2) := by
          by_cases hz : a + m = 0
          · rw [if_pos hz] at htime ⊢
            omega
          · rw [if_neg hz] at htime ⊢
            omega
        rw [hrun B]
        constructor
        · intro hc
          simp [rejectConfig, machine, UniformTM.step, qReject] at hc
        · exact fun heq => (hne heq).elim
    | accepted h8 htime hrun =>
        have hne : s ≠ (if a + m = 0 then 0 else 3 * (a + m) - 2) := by
          rw [if_neg (by omega : a + m ≠ 0)]
          subst s
          unfold deadline
          omega
        rw [hrun B]
        constructor
        · intro hc
          simp [acceptConfig, machine, UniformTM.step, qAccept] at hc
        · exact fun heq => (hne heq).elim
  · intro B
    rw [run_deadline]
    rfl
  · intro B i hi
    rw [run_deadline]
    exact base_blank x w hi i.2
  · intro B extra
    rw [machine.run_add, run_deadline]
    by_cases htag : tagMatches (Fin.append x w) = true
    · rw [machine.run_accept (finalConfig B x w) (by
        simp [finalConfig, htag, machine])]
    · have htag' : tagMatches (Fin.append x w) = false := Bool.eq_false_of_not_eq_true htag
      rw [machine.run_reject (finalConfig B x w) (by
        simp [finalConfig, htag', machine])]
  · intro B B' s hs
    dsimp
    cases run_shape x w s hs with
    | start _ hrun =>
        rw [hrun B, hrun B']
        refine ⟨rfl, rfl, fun i i' hii => ?_⟩
        exact baseTape_independent x w i i' hii
    | emptyProbe _ _ hrun =>
        rw [hrun B, hrun B']
        refine ⟨rfl, rfl, fun i i' hii => ?_⟩
        exact baseTape_independent x w i i' hii
    | probe _ _ _ _ hrun =>
        rw [hrun B, hrun B']
        refine ⟨rfl, rfl, fun i i' hii => ?_⟩
        exact baseTape_independent x w i i' hii
    | check _ _ _ _ hrun =>
        rw [hrun B, hrun B']
        refine ⟨rfl, rfl, fun i i' hii => ?_⟩
        exact erasedTape_independent x w _ i i' hii
    | ret _ _ _ _ hrun =>
        rw [hrun B, hrun B']
        refine ⟨rfl, rfl, fun i i' hii => ?_⟩
        exact erasedTape_independent x w _ i i' hii
    | tag _ _ _ _ _ _ hrun =>
        rw [hrun B, hrun B']
        refine ⟨rfl, rfl, fun i i' hii => ?_⟩
        exact baseTape_independent x w i i' hii
    | rejected _ _ _ hrun =>
        rw [hrun B, hrun B']
        refine ⟨rfl, rfl, fun i i' hii => ?_⟩
        exact baseTape_independent x w i i' hii
    | accepted _ _ hrun =>
        rw [hrun B, hrun B']
        refine ⟨rfl, rfl, fun i i' hii => ?_⟩
        exact baseTape_independent x w i i' hii
end FixedContentTagGate
end Pnp3.Complexity.Uniform.V1
