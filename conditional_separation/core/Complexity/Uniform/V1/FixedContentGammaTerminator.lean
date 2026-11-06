import Complexity.Uniform.V1.FixedContentTagGate
import Mathlib.Data.Fintype.Card

namespace Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator

open PairEncoding

abbrev stateCount : Nat := 3
def qScan : Fin stateCount := ⟨0, by decide⟩
def qAccept : Fin stateCount := ⟨1, by decide⟩
def qReject : Fin stateCount := ⟨2, by decide⟩

private def raw (q : Fin stateCount) (s : Option Bool) :
    Fin stateCount × Option Bool × Move :=
  match q.1 with
  | 0 => match s with
    | some false => (qScan, some false, .right)
    | some true => (qAccept, some true, .stay)
    | none => (qReject, none, .stay)
  | 1 => (qAccept, s, .stay)
  | _ => (qReject, s, .stay)

def machine : UniformTM where
  stateCount := stateCount
  start := qScan
  accept := qAccept
  reject := qReject
  accept_ne_reject := by decide
  rawStep := raw

/-- Search the physical suffix, returning the zero-run length before its first
`true`.  This is a specification of the scan result, not machine control. -/
private def gammaZerosAux? {L : Nat} (z : Bitstring L) (offset : Nat) : Nat → Option Nat
  | 0 => none
  | fuel + 1 =>
      match FixedContentTagGate.physicalSymbol z offset with
      | some true => some 0
      | some false => (gammaZerosAux? z (offset + 1) fuel).map Nat.succ
      | none => none

def gammaZeros? {L : Nat} (z : Bitstring L) : Option Nat :=
  gammaZerosAux? z 8 (L - 8)

def terminalIndex {L : Nat} (z : Bitstring L) : Nat :=
  match gammaZeros? z with
  | some zeros => 8 + zeros
  | none => L

def retag {N B : Nat} (c : Config FixedContentTagGate.stateCount N B) :
    Config stateCount N B where
  state := qScan
  head := c.head
  tape := c.tape

def startConfig {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) :
    Config stateCount (pairLength a m) B :=
  retag (FixedContentTagGate.finalConfig B x w)

def deadline (a m : Nat) : Nat := a + m - 7

private def baseTape {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) :=
  FixedPairContentMarkerErase.contentTape B x w

private def scanConfig {a m : Nat} (B : Nat) (x : Bitstring a)
    (w : Bitstring m) (j : Nat) (hj : j ≤ a + m) :
    Config stateCount (pairLength a m) B where
  state := qScan
  head := ⟨j, by unfold tapeLength pairLength; omega⟩
  tape := baseTape B x w

private def acceptConfig {a m : Nat} (B : Nat) (x : Bitstring a)
    (w : Bitstring m) (j : Nat) (hj : j < a + m) :
    Config stateCount (pairLength a m) B where
  state := qAccept
  head := ⟨j, by unfold tapeLength pairLength; omega⟩
  tape := baseTape B x w

private def rejectConfig {a m : Nat} (B : Nat) (x : Bitstring a)
    (w : Bitstring m) : Config stateCount (pairLength a m) B where
  state := qReject
  head := ⟨a + m, by unfold tapeLength pairLength; omega⟩
  tape := baseTape B x w

def finalConfig {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) :
    Config stateCount (pairLength a m) B where
  state := if (gammaZeros? (Fin.append x w)).isSome then qAccept else qReject
  head := ⟨min (terminalIndex (Fin.append x w)) (a + m), by
    unfold tapeLength pairLength; omega⟩
  tape := baseTape B x w

theorem table_and_resource_pins :
    (∀ s, machine.rawStep qScan s = match s with
      | some false => (qScan, some false, .right)
      | some true => (qAccept, some true, .stay)
      | none => (qReject, none, .stay)) ∧
    machine.stateCount = 3 ∧ machine.start = qScan ∧
    machine.accept = qAccept ∧ machine.reject = qReject ∧
    qScan.val = 0 ∧ qAccept.val = 1 ∧ qReject.val = 2 ∧
    Fintype.card (Fin machine.stateCount × Option Bool) = 9 := by
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  · intro s; cases s with
    | none => rfl
    | some b => cases b <;> rfl
  · decide

private theorem tag_length {L : Nat} (z : Bitstring L)
    (h : FixedContentTagGate.tagMatches z = true) : 8 ≤ L := by
  rcases FixedContentTagGate.tag_contract z with
    ⟨_, _, _, _, _, _, _, _, _, hlength⟩
  exact hlength h

private theorem config_ext {N B : Nat} {c d : Config stateCount N B}
    (hs : c.state = d.state) (hh : c.head = d.head) (ht : c.tape = d.tape) : c = d := by
  cases c; cases d; cases hs; cases hh; cases ht; rfl

private theorem step_keep {N B : Nat} (c : Config stateCount N B)
    (q' : Fin stateCount) (mv : Move)
    (h : machine.step c.state (c.tape c.head) = (q', c.tape c.head, mv)) :
    machine.stepConfig c =
      ({ state := q', head := moveHead c.head mv, tape := c.tape } :
        Config stateCount N B) := by
  apply config_ext
  · change (machine.step c.state (c.tape c.head)).1 = q'; rw [h]
  · change moveHead c.head (machine.step c.state (c.tape c.head)).2.2 = _; rw [h]
  · funext i
    change (if i = c.head then (machine.step c.state (c.tape c.head)).2.1
      else c.tape i) = c.tape i
    rw [h]
    by_cases hi : i = c.head <;> simp [hi]

private theorem base_read {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    {j : Nat} (hj : j < a + m) :
    baseTape B x w ⟨j, by unfold tapeLength pairLength; omega⟩ =
      some ((Fin.append x w) ⟨j, hj⟩) := by
  simp [baseTape, FixedPairContentMarkerErase.contentTape, hj]

private theorem base_blank {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    baseTape B x w ⟨a + m, by unfold tapeLength pairLength; omega⟩ = none := by
  simp [baseTape, FixedPairContentMarkerErase.contentTape]

private theorem step_scan_false {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (j : Nat) (hj : j < a + m) (hb : (Fin.append x w) ⟨j, hj⟩ = false) :
    machine.stepConfig (scanConfig B x w j (Nat.le_of_lt hj)) =
      scanConfig B x w (j + 1) (by omega) := by
  have hread := base_read (B := B) x w hj
  have hstep : machine.step (scanConfig B x w j (Nat.le_of_lt hj)).state
      ((scanConfig B x w j (Nat.le_of_lt hj)).tape
        (scanConfig B x w j (Nat.le_of_lt hj)).head) =
      (qScan, (scanConfig B x w j (Nat.le_of_lt hj)).tape
        (scanConfig B x w j (Nat.le_of_lt hj)).head, .right) := by
    change machine.step qScan (baseTape B x w ⟨j, _⟩) = _
    simp [scanConfig, hread, hb, machine, UniformTM.step, qScan, qAccept,
      qReject, raw]
  rw [step_keep _ qScan .right hstep]
  apply config_ext <;> try rfl
  apply Fin.ext
  simp [scanConfig, moveHead, show j + 1 < tapeLength (pairLength a m) B by
    unfold tapeLength pairLength; omega]

private theorem step_scan_true {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (j : Nat) (hj : j < a + m) (hb : (Fin.append x w) ⟨j, hj⟩ = true) :
    machine.stepConfig (scanConfig B x w j (Nat.le_of_lt hj)) =
      acceptConfig B x w j hj := by
  have hread := base_read (B := B) x w hj
  have hstep : machine.step (scanConfig B x w j (Nat.le_of_lt hj)).state
      ((scanConfig B x w j (Nat.le_of_lt hj)).tape
        (scanConfig B x w j (Nat.le_of_lt hj)).head) =
      (qAccept, (scanConfig B x w j (Nat.le_of_lt hj)).tape
        (scanConfig B x w j (Nat.le_of_lt hj)).head, .stay) := by
    change machine.step qScan (baseTape B x w ⟨j, _⟩) = _
    simp [scanConfig, hread, hb, machine, UniformTM.step, qScan, qAccept,
      qReject, raw]
  rw [step_keep _ qAccept .stay hstep]
  rfl

private theorem step_scan_blank {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    machine.stepConfig (scanConfig B x w (a + m) (le_refl _)) = rejectConfig B x w := by
  have hread := base_blank (B := B) x w
  have hstep : machine.step (scanConfig B x w (a + m) (le_refl _)).state
      ((scanConfig B x w (a + m) (le_refl _)).tape
        (scanConfig B x w (a + m) (le_refl _)).head) =
      (qReject, (scanConfig B x w (a + m) (le_refl _)).tape
        (scanConfig B x w (a + m) (le_refl _)).head, .stay) := by
    change machine.step qScan (baseTape B x w ⟨a + m, _⟩) = _
    simp [scanConfig, hread, machine, UniformTM.step, qScan, qAccept,
      qReject, raw]
  rw [step_keep _ qReject .stay hstep]
  rfl

private theorem gate_final_head {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true) :
    (FixedContentTagGate.finalConfig B x w).head.val = 8 := by
  have hb := htag
  simp only [FixedContentTagGate.tagMatches, decide_eq_true_eq] at hb
  have hL := tag_length (Fin.append x w) htag
  simp [FixedContentTagGate.finalConfig, hb, hL]

private theorem tag_start {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true) :
    startConfig B x w = scanConfig B x w 8
      (tag_length (Fin.append x w) htag) := by
  apply config_ext
  · rfl
  · apply Fin.ext
    exact gate_final_head x w htag
  · rfl

private theorem run_prefix_false {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hL : 8 ≤ a + m)
    (s : Nat) (hs : s ≤ a + m - 8)
    (hfalse : ∀ i, (hi : i < s) → (Fin.append x w) ⟨8 + i, by omega⟩ = false) :
    machine.run s (startConfig B x w) = scanConfig B x w (8 + s) (by omega) := by
  induction s with
  | zero => simpa using tag_start (B := B) x w htag
  | succ s ih =>
      rw [UniformTM.run, ih (by omega) (fun i hi => hfalse i (by omega))]
      apply step_scan_false
      exact hfalse s (by omega)

private theorem gammaAux_some_specs {L : Nat} (z : Bitstring L) :
    ∀ offset fuel zeros, gammaZerosAux? z offset fuel = some zeros →
      zeros < fuel ∧
      FixedContentTagGate.physicalSymbol z (offset + zeros) = some true ∧
      ∀ i, i < zeros → FixedContentTagGate.physicalSymbol z (offset + i) = some false := by
  intro offset fuel
  induction fuel generalizing offset with
  | zero => simp [gammaZerosAux?]
  | succ fuel ih =>
      intro zeros h
      rw [gammaZerosAux?] at h
      cases hp : FixedContentTagGate.physicalSymbol z offset with
      | none => simp [hp] at h
      | some b =>
        cases b with
        | true =>
          simp [hp] at h
          subst zeros
          exact ⟨by omega, by simpa using hp, fun i hi => by omega⟩
        | false =>
          simp [hp] at h
          rcases h with ⟨n, hn, hzeros⟩
          subst zeros
          rcases ih (offset + 1) n hn with ⟨hlt, ht, hz⟩
          refine ⟨by omega, ?_, ?_⟩
          · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht
          intro i hi
          cases i with
          | zero => simpa using hp
          | succ i => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
              using hz i (by omega)

private theorem gamma_some_specs {L : Nat} (z : Bitstring L) {zeros : Nat}
    (h : gammaZeros? z = some zeros) :
    8 + zeros < L ∧
    FixedContentTagGate.physicalSymbol z (8 + zeros) = some true ∧
    ∀ i, i < zeros → FixedContentTagGate.physicalSymbol z (8 + i) = some false := by
  rcases gammaAux_some_specs z 8 (L - 8) zeros h with ⟨hlt, ht, hz⟩
  exact ⟨by omega, ht, hz⟩

private theorem gammaAux_none_specs {L : Nat} (z : Bitstring L) :
    ∀ offset fuel, offset + fuel ≤ L → gammaZerosAux? z offset fuel = none →
      ∀ i, i < fuel → FixedContentTagGate.physicalSymbol z (offset + i) = some false := by
  intro offset fuel
  induction fuel generalizing offset with
  | zero => simp
  | succ fuel ih =>
      intro hfit h i hi
      rw [gammaZerosAux?] at h
      have hoff : offset < L := by omega
      cases hp : FixedContentTagGate.physicalSymbol z offset with
      | none => simp [FixedContentTagGate.physicalSymbol, hoff] at hp
      | some b =>
        cases b with
        | true => simp [hp] at h
        | false =>
          simp [hp] at h
          cases i with
          | zero => simpa using hp
          | succ i =>
            have hrec := ih (offset + 1) (by omega) h i (by omega)
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrec

private theorem gamma_none_specs {L : Nat} (z : Bitstring L) (hL : 8 ≤ L)
    (h : gammaZeros? z = none) :
    ∀ i, i < L - 8 → FixedContentTagGate.physicalSymbol z (8 + i) = some false := by
  exact gammaAux_none_specs z 8 (L - 8) (by omega) h

theorem gamma_contract {L : Nat} (z : Bitstring L) :
    (∀ zeros, gammaZeros? z = some zeros →
      8 + zeros < L ∧
      FixedContentTagGate.physicalSymbol z (8 + zeros) = some true ∧
      ∀ i, i < zeros → FixedContentTagGate.physicalSymbol z (8 + i) = some false) ∧
    (8 ≤ L → gammaZeros? z = none →
      ∀ i, i < L - 8 → FixedContentTagGate.physicalSymbol z (8 + i) = some false) ∧
    terminalIndex z ≤ L := by
  refine ⟨fun _ h => gamma_some_specs z h, gamma_none_specs z, ?_⟩
  unfold terminalIndex
  split
  · rename_i h; exact Nat.le_of_lt (gamma_some_specs z h).1
  · exact le_rfl

theorem handoff_exact {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true) :
    let p := FixedContentTagGate.machine.run (FixedContentTagGate.deadline a m)
      (FixedContentTagGate.startConfig B x w)
    let c := startConfig B x w
    p = FixedContentTagGate.finalConfig B x w ∧
    p.state = FixedContentTagGate.machine.accept ∧ p.head.val = 8 ∧
    p.tape = FixedPairContentMarkerErase.contentTape B x w ∧
    c = retag p ∧ c.state = machine.start ∧ c.head = p.head ∧ c.tape = p.tape := by
  dsimp
  rw [FixedContentTagGate.run_deadline]
  refine ⟨rfl, ?_, gate_final_head x w htag, rfl, rfl, rfl, rfl, rfl⟩
  change (if FixedContentTagGate.tagMatches (Fin.append x w) then
    FixedContentTagGate.machine.accept else FixedContentTagGate.machine.reject) =
      FixedContentTagGate.machine.accept
  simp [htag]

theorem run_deadline {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true) :
    machine.run (deadline a m) (startConfig B x w) = finalConfig B x w := by
  have hL := tag_length (Fin.append x w) htag
  cases hg : gammaZeros? (Fin.append x w) with
  | some zeros =>
      rcases gamma_some_specs _ hg with ⟨hlt, ht, hz⟩
      have hr := run_prefix_false (B := B) x w htag hL zeros (by omega) (fun i hi => by
        have := hz i hi
        simpa [FixedContentTagGate.physicalSymbol, show 8 + i < a + m by omega] using this)
      rw [show deadline a m = zeros + 1 + (deadline a m - (zeros + 1)) by
        unfold deadline; omega, machine.run_add, UniformTM.run, hr]
      rw [step_scan_true x w (8 + zeros) hlt (by
        simpa [FixedContentTagGate.physicalSymbol, hlt] using ht)]
      rw [machine.run_accept]
      · apply config_ext
        · simp [acceptConfig, finalConfig, hg]
        · apply Fin.ext
          simp [acceptConfig, finalConfig, terminalIndex, hg,
            Nat.min_eq_left (Nat.le_of_lt hlt)]
        · rfl
      · rfl
  | none =>
      have hz := gamma_none_specs _ hL hg
      have hr := run_prefix_false (B := B) x w htag hL (a + m - 8) (le_rfl)
        (fun i hi => by
          have hfit : 8 + i < a + m := by omega
          simpa [FixedContentTagGate.physicalSymbol, hfit] using hz i hi)
      have hsum : 8 + (a + m - 8) = a + m := by omega
      rw [show deadline a m = (a + m - 8) + 1 by unfold deadline; omega,
        UniformTM.run, hr]
      have hs := step_scan_blank (B := B) x w
      calc
        machine.stepConfig (scanConfig B x w (8 + (a + m - 8)) (by omega)) =
            rejectConfig B x w := by simpa only [hsum] using hs
        _ = finalConfig B x w := by
          apply config_ext
          · simp [rejectConfig, finalConfig, hg]
          · apply Fin.ext; simp [rejectConfig, finalConfig, terminalIndex, hg]
          · rfl

/-- The common absorbing deadline is exactly one step beyond the physical
suffix scan length. -/
theorem deadline_exact (a m : Nat) :
    8 ≤ a + m → deadline a m = (a + m - 8) + 1 := by
  intro hL
  unfold deadline
  omega

theorem exact_terminal_contract {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true) :
    (∀ zeros, gammaZeros? (Fin.append x w) = some zeros →
      (∀ s < zeros + 1,
        (machine.run s (startConfig B x w)).state ≠ machine.accept ∧
        (machine.run s (startConfig B x w)).state ≠ machine.reject) ∧
      machine.run (zeros + 1) (startConfig B x w) =
        finalConfig B x w ∧ zeros + 1 ≤ deadline a m) ∧
    (gammaZeros? (Fin.append x w) = none →
      (∀ s < deadline a m,
        (machine.run s (startConfig B x w)).state ≠ machine.accept ∧
        (machine.run s (startConfig B x w)).state ≠ machine.reject) ∧
      machine.run (deadline a m) (startConfig B x w) = finalConfig B x w) := by
  constructor
  · intro zeros hg
    rcases gamma_some_specs _ hg with ⟨hlt, _, hz⟩
    refine ⟨?_, ?_, by unfold deadline; omega⟩
    · intro s hs
      rw [run_prefix_false (B := B) x w htag (tag_length _ htag) s (by omega) (fun i hi => by
        have hp := hz i (by omega)
        simpa [FixedContentTagGate.physicalSymbol, show 8 + i < a + m by omega] using hp)]
      change qScan ≠ qAccept ∧ qScan ≠ qReject
      decide
    · rw [UniformTM.run, run_prefix_false (B := B) x w htag (tag_length _ htag) zeros (by omega)
          (fun i hi => by
            have hp := hz i hi
            simpa [FixedContentTagGate.physicalSymbol, show 8 + i < a + m by omega] using hp),
        step_scan_true x w (8 + zeros) hlt]
      · apply config_ext
        · simp [acceptConfig, finalConfig, hg]
        · apply Fin.ext
          simp [acceptConfig, finalConfig, terminalIndex, hg,
            Nat.min_eq_left (Nat.le_of_lt hlt)]
        · rfl
      · have ht := (gamma_some_specs _ hg).2.1
        simpa [FixedContentTagGate.physicalSymbol, hlt] using ht
  · intro hg
    refine ⟨?_, run_deadline x w htag⟩
    intro s hs
    have hL := tag_length (Fin.append x w) htag
    have hz := gamma_none_specs _ hL hg
    rw [run_prefix_false (B := B) x w htag hL s (by unfold deadline at hs; omega)
      (fun i hi => by
        simpa [FixedContentTagGate.physicalSymbol, show 8 + i < a + m by
          unfold deadline at hs; omega] using hz i (by unfold deadline at hs; omega))]
    change qScan ≠ qAccept ∧ qScan ≠ qReject
    decide

private def stopTime {L : Nat} (z : Bitstring L) : Nat :=
  match gammaZeros? z with
  | some zeros => zeros + 1
  | none => L - 7

private theorem run_at_most_deadline {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (s : Nat) (hs : s ≤ deadline a m) :
    (s < stopTime (Fin.append x w) →
      ∃ hfit : 8 + s ≤ a + m,
        machine.run s (startConfig B x w) = scanConfig B x w (8 + s) hfit) ∧
    (stopTime (Fin.append x w) ≤ s →
      machine.run s (startConfig B x w) = finalConfig B x w) := by
  constructor
  · intro hpre
    cases hg : gammaZeros? (Fin.append x w) with
    | some zeros =>
        rcases gamma_some_specs _ hg with ⟨hlt, _, hz⟩
        have hstop : stopTime (Fin.append x w) = zeros + 1 := by simp [stopTime, hg]
        have hfit : 8 + s ≤ a + m := by omega
        exact ⟨hfit, run_prefix_false (B := B) x w htag (tag_length _ htag) s
          (by omega) (fun i hi => by
            have hp := hz i (by omega)
            simpa [FixedContentTagGate.physicalSymbol,
              show 8 + i < a + m by omega] using hp)⟩
    | none =>
        have hstop : stopTime (Fin.append x w) = a + m - 7 := by simp [stopTime, hg]
        have hfit : 8 + s ≤ a + m := by unfold deadline at hs; omega
        exact ⟨hfit, run_prefix_false (B := B) x w htag (tag_length _ htag) s
          (by omega) (fun i hi => by
            have hp := gamma_none_specs _ (tag_length _ htag) hg i (by omega)
            simpa [FixedContentTagGate.physicalSymbol,
              show 8 + i < a + m by omega] using hp)⟩
  · intro hpost
    cases hg : gammaZeros? (Fin.append x w) with
    | some zeros =>
        have hstop : stopTime (Fin.append x w) = zeros + 1 := by simp [stopTime, hg]
        rw [show s = zeros + 1 + (s - (zeros + 1)) by omega, machine.run_add,
          (exact_terminal_contract (B := B) x w htag).1 zeros hg |>.2.1]
        apply machine.run_accept
        simp [finalConfig, hg, machine]
    | none =>
        have hstop : stopTime (Fin.append x w) = deadline a m := by
          simp [stopTime, hg, deadline]
        have : s = deadline a m := by omega
        subst s
        exact run_deadline x w htag

theorem phase_contract {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true) :
    (∀ B s, s ≤ deadline a m →
      (machine.run s (startConfig B x w)).head.val ≤ a + m) ∧
    (∀ B s, s < deadline a m →
      let c := machine.run s (startConfig B x w)
      let move := (machine.step c.state (c.tape c.head)).2.2
      move ≠ .left ∧
      (move = .right → c.head.val + 1 < tapeLength (pairLength a m) B)) ∧
    (∀ B, (machine.run (deadline a m) (startConfig B x w)).tape =
      FixedPairContentMarkerErase.contentTape B x w) ∧
    (∀ B (i : Fin (tapeLength (pairLength a m) B)), a + m ≤ i.val →
      (machine.run (deadline a m) (startConfig B x w)).tape i = none) ∧
    (∀ B extra, machine.run (deadline a m + extra) (startConfig B x w) =
      finalConfig B x w) ∧
    (∀ B B' s, s ≤ deadline a m →
      let c := machine.run s (startConfig B x w)
      let c' := machine.run s (startConfig B' x w)
      c.state = c'.state ∧ c.head.val = c'.head.val ∧
      ∀ (i : Fin (tapeLength (pairLength a m) B))
        (i' : Fin (tapeLength (pairLength a m) B')),
        i.val = i'.val →
        c.tape i = c'.tape i') := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro B s hs
    by_cases hpre : s < stopTime (Fin.append x w)
    · rcases (run_at_most_deadline x w htag s hs).1 hpre with ⟨hfit, hrun⟩
      rw [hrun]
      simpa [scanConfig] using hfit
    · rw [(run_at_most_deadline x w htag s hs).2 (by omega)]
      simp [finalConfig]
  · intro B s hs
    dsimp
    by_cases hpre : s < stopTime (Fin.append x w)
    · rcases (run_at_most_deadline x w htag s (Nat.le_of_lt hs)).1 hpre with
        ⟨hfit, hrun⟩
      rw [hrun]
      have hroom : 8 + s + 1 < tapeLength (pairLength a m) B := by
        unfold tapeLength pairLength
        omega
      constructor
      · simp only [scanConfig, machine, UniformTM.step, raw, qScan]
        simp only [Fin.mk.injEq, qAccept, qReject, OfNat.ofNat, reduceCtorEq,
          ↓reduceIte]
        split <;> simp
      · intro _
        simpa [scanConfig] using hroom
    · rw [(run_at_most_deadline x w htag s (Nat.le_of_lt hs)).2 (by omega)]
      cases hg : gammaZeros? (Fin.append x w) with
      | some zeros =>
          simp [finalConfig, hg, machine, UniformTM.step, qAccept]
      | none =>
          simp [finalConfig, hg, machine, UniformTM.step, qReject]
  · intro B
    rw [run_deadline x w htag]
    rfl
  · intro B i hi
    rw [run_deadline x w htag]
    simp [finalConfig, baseTape, FixedPairContentMarkerErase.contentTape,
      Nat.not_lt_of_ge hi]
  · intro B extra
    rw [machine.run_add, run_deadline x w htag]
    by_cases hg : (gammaZeros? (Fin.append x w)).isSome
    · have hs : (finalConfig B x w).state = machine.accept := by
        simp [finalConfig, hg, machine]
      rw [machine.run_accept (finalConfig B x w) hs]
    · have hs : (finalConfig B x w).state = machine.reject := by
        simp [finalConfig, hg, machine]
      rw [machine.run_reject (finalConfig B x w) hs]
  · intro B B' s hs
    by_cases hpre : s < stopTime (Fin.append x w)
    · rcases (run_at_most_deadline (B := B) x w htag s hs).1 hpre with ⟨_, hr⟩
      rcases (run_at_most_deadline (B := B') x w htag s hs).1 hpre with ⟨_, hr'⟩
      rw [hr, hr']
      refine ⟨rfl, rfl, ?_⟩
      intro i i' hii
      simp [scanConfig, baseTape, FixedPairContentMarkerErase.contentTape, hii]
    · rw [(run_at_most_deadline (B := B) x w htag s hs).2 (by omega),
        (run_at_most_deadline (B := B') x w htag s hs).2 (by omega)]
      refine ⟨rfl, rfl, ?_⟩
      intro i i' hii
      simp [finalConfig, baseTape, FixedPairContentMarkerErase.contentTape, hii]
end Pnp3.Complexity.Uniform.V1.FixedContentGammaTerminator
