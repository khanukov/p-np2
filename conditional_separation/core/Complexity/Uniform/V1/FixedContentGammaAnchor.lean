import Complexity.Uniform.V1.FixedContentGammaTerminator
import Mathlib.Data.Fintype.Card

/-!
# Fixed-content gamma anchor (Part A G2a)

This six-state phase starts from the merged G1 final configuration.  On a
physical gamma terminator it walks left over the zero run, recognizes the
fixed tag tail `cell 6 = true, cell 7 = false`, erases exactly cell 7 as a
recoverable marker, and returns to accept on the same terminator.  It does not
read or decode the gamma payload.

The marker creates the explicit G2b obligation: no later counter-zone step may
write `none`, and cell 7 must be restored before entering any phase whose
precondition is the literal `contentTape`.
-/

namespace Pnp3.Complexity.Uniform.V1.FixedContentGammaAnchor

open PairEncoding

abbrev stateCount : Nat := 6
def qStart : Fin stateCount := ⟨0, by decide⟩
def qLeft : Fin stateCount := ⟨1, by decide⟩
def qErase : Fin stateCount := ⟨2, by decide⟩
def qReturn : Fin stateCount := ⟨3, by decide⟩
def qAccept : Fin stateCount := ⟨4, by decide⟩
def qReject : Fin stateCount := ⟨5, by decide⟩

private def raw (q : Fin stateCount) (s : Option Bool) :
    Fin stateCount × Option Bool × Move :=
  match q.1 with
  | 0 => match s with
    | some true => (qLeft, some true, .left)
    | s => (qReject, s, .stay)
  | 1 => match s with
    | some false => (qLeft, some false, .left)
    | some true => (qErase, some true, .right)
    | none => (qReject, none, .stay)
  | 2 => match s with
    | some false => (qReturn, none, .right)
    | s => (qReject, s, .stay)
  | 3 => match s with
    | some false => (qReturn, some false, .right)
    | some true => (qAccept, some true, .stay)
    | none => (qReject, none, .stay)
  | 4 => (qAccept, s, .stay)
  | _ => (qReject, s, .stay)

def machine : UniformTM where
  stateCount := stateCount
  start := qStart
  accept := qAccept
  reject := qReject
  accept_ne_reject := by decide
  rawStep := raw

def retag {N B : Nat} (c : Config FixedContentGammaTerminator.stateCount N B) :
    Config stateCount N B := ⟨qStart, c.head, c.tape⟩

def startConfig {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) :
    Config stateCount (pairLength a m) B :=
  retag (FixedContentGammaTerminator.finalConfig B x w)

def successTime (zeros : Nat) : Nat := 2 * zeros + 5
def deadline (a m : Nat) : Nat := 2 * (a + m)

def markedTape {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) :
    Fin (tapeLength (pairLength a m) B) → Option Bool := fun i =>
  if i.1 = 7 then none else FixedPairContentMarkerErase.contentTape B x w i

def finalConfig {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) :
    Config stateCount (pairLength a m) B := ⟨
  if (FixedContentGammaTerminator.gammaZeros? (Fin.append x w)).isSome then qAccept else qReject,
  ⟨min (FixedContentGammaTerminator.terminalIndex (Fin.append x w)) (a + m), by
    unfold tapeLength pairLength; omega⟩,
  if (FixedContentGammaTerminator.gammaZeros? (Fin.append x w)).isSome then
    markedTape B x w else FixedPairContentMarkerErase.contentTape B x w⟩

theorem table_and_resource_pins :
    (∀ s, machine.step qStart s = match s with
      | some true => (qLeft, some true, .left)
      | some false => (qReject, some false, .stay)
      | none => (qReject, none, .stay)) ∧
    (∀ s, machine.step qLeft s = match s with
      | some false => (qLeft, some false, .left)
      | some true => (qErase, some true, .right)
      | none => (qReject, none, .stay)) ∧
    (∀ s, machine.step qErase s = match s with
      | some false => (qReturn, none, .right)
      | some true => (qReject, some true, .stay)
      | none => (qReject, none, .stay)) ∧
    (∀ s, machine.step qReturn s = match s with
      | some false => (qReturn, some false, .right)
      | some true => (qAccept, some true, .stay)
      | none => (qReject, none, .stay)) ∧
    (∀ s, machine.step qAccept s = (qAccept, s, .stay)) ∧
    (∀ s, machine.step qReject s = (qReject, s, .stay)) ∧
    machine.stateCount = 6 ∧ machine.start = qStart ∧
    machine.accept = qAccept ∧ machine.reject = qReject ∧
    qStart.val = 0 ∧ qLeft.val = 1 ∧ qErase.val = 2 ∧ qReturn.val = 3 ∧
    qAccept.val = 4 ∧ qReject.val = 5 ∧
    Fintype.card (Fin machine.stateCount × Option Bool) = 18 := by
  refine ⟨fun s => by cases s with | none => decide | some b => cases b <;> decide,
    fun s => by cases s with | none => decide | some b => cases b <;> decide,
    fun s => by cases s with | none => decide | some b => cases b <;> decide,
    fun s => by cases s with | none => decide | some b => cases b <;> decide,
    fun s => by cases s with | none => decide | some b => cases b <;> decide,
    fun s => by cases s with | none => decide | some b => cases b <;> decide,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  decide

private theorem start_true_action : machine.step qStart (some true) =
    (qLeft, some true, .left) := by decide
private theorem start_blank_action : machine.step qStart none = (qReject, none, .stay) := by decide
private theorem left_false_action : machine.step qLeft (some false) =
    (qLeft, some false, .left) := by decide
private theorem left_true_action : machine.step qLeft (some true) =
    (qErase, some true, .right) := by decide
private theorem erase_false_action : machine.step qErase (some false) =
    (qReturn, none, .right) := by decide
private theorem return_false_action : machine.step qReturn (some false) =
    (qReturn, some false, .right) := by decide
private theorem return_true_action : machine.step qReturn (some true) =
    (qAccept, some true, .stay) := by decide

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

private theorem step_keep {N B : Nat} (c : Config stateCount N B)
    (q' : Fin stateCount) (s : Option Bool) (mv : Move)
    (hr : c.tape c.head = s) (h : machine.step c.state s = (q', s, mv)) :
    machine.stepConfig c = ⟨q', moveHead c.head mv, c.tape⟩ := by
  rw [step_eq c q' s mv (by simpa [hr] using h)]
  congr 1
  funext i
  by_cases hi : i = c.head <;> simp [hi, hr]

private def baseTape {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) :=
  FixedPairContentMarkerErase.contentTape B x w

private theorem base_read {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    {j : Nat} (hj : j < a + m) :
    baseTape B x w ⟨j, by unfold tapeLength pairLength; omega⟩ =
      some ((Fin.append x w) ⟨j, hj⟩) := by
  simp [baseTape, FixedPairContentMarkerErase.contentTape, hj]

private theorem base_blank {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    baseTape B x w ⟨a + m, by unfold tapeLength pairLength; omega⟩ = none := by
  simp [baseTape, FixedPairContentMarkerErase.contentTape]

private def cfg {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m)
    (q : Fin stateCount) (j : Nat) (hj : j ≤ a + m)
    (t : Fin (tapeLength (pairLength a m) B) → Option Bool := baseTape B x w) :
    Config stateCount (pairLength a m) B :=
  ⟨q, ⟨j, by unfold tapeLength pairLength; omega⟩, t⟩

private theorem tag_cells {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true) :
    8 ≤ a + m ∧
      FixedContentTagGate.physicalSymbol (Fin.append x w) 6 = some true ∧
      FixedContentTagGate.physicalSymbol (Fin.append x w) 7 = some false := by
  rcases FixedContentTagGate.tag_contract (Fin.append x w) with
    ⟨_, _, _, _, _, _, _, _, hc, hlen⟩
  have hL := hlen htag
  have hc := hc.mp htag
  exact ⟨hL, by simpa [FixedContentTagGate.expectedTagBit] using hc ⟨6, by decide⟩,
    by simpa [FixedContentTagGate.expectedTagBit] using hc ⟨7, by decide⟩⟩

private theorem start_some {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    {zeros : Nat} (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros) :
    startConfig B x w = cfg B x w qStart (8 + zeros) (Nat.le_of_lt
      ((FixedContentGammaTerminator.gamma_contract _).1 zeros hg).1) := by
  apply config_ext
  · rfl
  · apply Fin.ext
    simp [startConfig, retag, FixedContentGammaTerminator.finalConfig, hg,
      FixedContentGammaTerminator.terminalIndex, cfg,
      Nat.min_eq_left (Nat.le_of_lt ((FixedContentGammaTerminator.gamma_contract _).1 zeros hg).1)]
  · rfl

private theorem start_none {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = none) :
    startConfig B x w = cfg B x w qStart (a + m) (le_rfl) := by
  apply config_ext
  · rfl
  · apply Fin.ext
    simp [startConfig, retag, FixedContentGammaTerminator.finalConfig, hg,
      FixedContentGammaTerminator.terminalIndex, cfg]
  · rfl

private theorem step_start_true {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (j : Nat) (hj : j < a + m) (hb : (Fin.append x w) ⟨j, hj⟩ = true) :
    machine.stepConfig (cfg B x w qStart j (Nat.le_of_lt hj)) =
      cfg B x w qLeft (j - 1) (by omega) := by
  have hr := base_read (B := B) x w hj
  rw [step_keep _ qLeft (some true) .left (by simpa [cfg, hb] using hr) start_true_action]
  apply config_ext
  · rfl
  · apply Fin.ext; simp [cfg, moveHead]
  · rfl

private theorem step_left_false {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (j : Nat) (hj : j < a + m) (hb : (Fin.append x w) ⟨j, hj⟩ = false) :
    machine.stepConfig (cfg B x w qLeft j (Nat.le_of_lt hj)) =
      cfg B x w qLeft (j - 1) (by omega) := by
  have hr := base_read (B := B) x w hj
  rw [step_keep _ qLeft (some false) .left (by simpa [cfg, hb] using hr) left_false_action]
  apply config_ext
  · rfl
  · apply Fin.ext; simp [cfg, moveHead]
  · rfl

private theorem step_left_true {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (hL : 8 ≤ a + m) (hb : (Fin.append x w) ⟨6, by omega⟩ = true) :
    machine.stepConfig (cfg B x w qLeft 6 (by omega)) = cfg B x w qErase 7 (by omega) := by
  have hr := base_read (B := B) x w (show 6 < a + m by omega)
  rw [step_keep _ qErase (some true) .right (by simpa [cfg, hb] using hr) left_true_action]
  apply config_ext
  · rfl
  · apply Fin.ext
    simp [cfg, moveHead, show 7 < tapeLength (pairLength a m) B by
      unfold tapeLength pairLength; omega]
  · rfl

private theorem step_erase {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (hL : 8 ≤ a + m) (hb : (Fin.append x w) ⟨7, by omega⟩ = false) :
    machine.stepConfig (cfg B x w qErase 7 (by omega)) =
      cfg B x w qReturn 8 (by omega) (markedTape B x w) := by
  have hr := base_read (B := B) x w (show 7 < a + m by omega)
  rw [step_eq _ qReturn none .right (by
    change machine.step qErase (baseTape B x w ⟨7, _⟩) = _
    rw [hr, hb]
    exact erase_false_action)]
  apply config_ext
  · rfl
  · apply Fin.ext
    simp [cfg, moveHead, show 8 < tapeLength (pairLength a m) B by
      unfold tapeLength pairLength; omega]
  · funext i
    simp only [cfg]
    by_cases hi : i.val = 7
    · have : i = ⟨7, by unfold tapeLength pairLength; omega⟩ := Fin.ext hi
      rw [this]; simp [markedTape]
    · have hn : i ≠ ⟨7, by unfold tapeLength pairLength; omega⟩ := by
        intro h; exact hi (congrArg Fin.val h)
      simp [markedTape, baseTape, hi, hn]

private theorem marked_read {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    {j : Nat} (hj : j < a + m) (hj7 : j ≠ 7) :
    markedTape B x w ⟨j, by unfold tapeLength pairLength; omega⟩ =
      some ((Fin.append x w) ⟨j, hj⟩) := by
  simp [markedTape, hj7, FixedPairContentMarkerErase.contentTape, hj]

private theorem step_return_false {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (j : Nat) (hj : j < a + m) (hj7 : j ≠ 7)
    (hb : (Fin.append x w) ⟨j, hj⟩ = false) :
    machine.stepConfig (cfg B x w qReturn j (Nat.le_of_lt hj) (markedTape B x w)) =
      cfg B x w qReturn (j + 1) (by omega) (markedTape B x w) := by
  have hr := marked_read (B := B) x w hj hj7
  rw [step_keep _ qReturn (some false) .right (by simpa [cfg, hb] using hr)
    return_false_action]
  apply config_ext
  · rfl
  · apply Fin.ext
    simp [cfg, moveHead, show j + 1 < tapeLength (pairLength a m) B by
      unfold tapeLength pairLength; omega]
  · rfl

private theorem step_return_true {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (j : Nat) (hj : j < a + m) (hj7 : j ≠ 7)
    (hb : (Fin.append x w) ⟨j, hj⟩ = true) :
    machine.stepConfig (cfg B x w qReturn j (Nat.le_of_lt hj) (markedTape B x w)) =
      cfg B x w qAccept j (Nat.le_of_lt hj) (markedTape B x w) := by
  have hr := marked_read (B := B) x w hj hj7
  rw [step_keep _ qAccept (some true) .stay (by simpa [cfg, hb] using hr)
    return_true_action]
  rfl

private theorem run_left_zeros {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    {zeros : Nat} (hlt : 8 + zeros < a + m)
    (hz : forall i, i < zeros ->
      FixedContentTagGate.physicalSymbol (Fin.append x w) (8 + i) = some false) :
    machine.run zeros (cfg B x w qLeft (7 + zeros) (by omega)) =
      cfg B x w qLeft 7 (by omega) := by
  induction zeros with
  | zero => rfl
  | succ zeros ih =>
      have hs : machine.run 1 (cfg B x w qLeft (7 + (zeros + 1)) (by omega)) =
          cfg B x w qLeft (7 + zeros) (by omega) := by
        rw [UniformTM.run]
        simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          step_left_false (B := B) x w (8 + zeros) (by omega) (by
            have hp := hz zeros (by omega)
            simpa [FixedContentTagGate.physicalSymbol,
              show 8 + zeros < a + m by omega] using hp)
      calc
        machine.run (zeros + 1) (cfg B x w qLeft (7 + (zeros + 1)) (by omega)) =
            machine.run zeros (machine.run 1
              (cfg B x w qLeft (7 + (zeros + 1)) (by omega))) := by
              nth_rewrite 1 [Nat.add_comm zeros 1]
              exact machine.run_add 1 zeros _
        _ = machine.run zeros (cfg B x w qLeft (7 + zeros) (by omega)) := by rw [hs]
        _ = cfg B x w qLeft 7 (by omega) := ih (by omega) (fun i hi => hz i (by omega))

private theorem run_left_prefix {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    {zeros r : Nat} (hlt : 8 + zeros < a + m) (hr : r ≤ zeros)
    (hz : ∀ i, i < zeros →
      FixedContentTagGate.physicalSymbol (Fin.append x w) (8 + i) = some false) :
    machine.run r (cfg B x w qLeft (7 + zeros) (by omega)) =
      cfg B x w qLeft (7 + zeros - r) (by omega) := by
  induction r with
  | zero => rfl
  | succ r ih =>
      have hhead : 7 + zeros - r < a + m := by omega
      rw [UniformTM.run, ih (by omega)]
      exact step_left_false (B := B) x w (7 + zeros - r) hhead (by
      have hp := hz (zeros - (r + 1)) (by omega)
      simpa [FixedContentTagGate.physicalSymbol,
        show 7 + zeros - r = 8 + (zeros - (r + 1)) by omega,
        show 8 + (zeros - (r + 1)) < a + m by omega] using hp)

private theorem run_success_pre_left {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    {zeros s : Nat}
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hs0 : 0 < s) (hs : s < zeros + 2) :
    machine.run s (startConfig B x w) =
      cfg B x w qLeft (8 + zeros - s) (by
        have := ((FixedContentGammaTerminator.gamma_contract _).1 zeros hg).1
        omega) := by
  rcases (FixedContentGammaTerminator.gamma_contract _).1 zeros hg with ⟨hlt, ht, hz⟩
  have hone : machine.run 1 (startConfig B x w) =
      cfg B x w qLeft (7 + zeros) (by omega) := by
    rw [UniformTM.run, start_some (B := B) x w hg]
    change machine.stepConfig (cfg B x w qStart (8 + zeros) _) = _
    rw [step_start_true (B := B) x w (8 + zeros) hlt (by
      simpa [FixedContentTagGate.physicalSymbol, hlt] using ht)]
    apply config_ext
    · rfl
    · apply Fin.ext; simp
    · rfl
  calc
    machine.run s (startConfig B x w) =
        machine.run (s - 1) (machine.run 1 (startConfig B x w)) := by
          rw [← machine.run_add]; congr
          omega
    _ = cfg B x w qLeft (7 + zeros - (s - 1)) (by omega) := by
          rw [hone, run_left_prefix x w hlt (by omega) hz]
    _ = cfg B x w qLeft (8 + zeros - s) (by omega) := by
      apply config_ext
      · rfl
      · apply Fin.ext
        change 7 + zeros - (s - 1) = 8 + zeros - s
        omega
      · rfl

private theorem run_left {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    {zeros : Nat} (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros) :
    machine.run (zeros + 2) (startConfig B x w) = cfg B x w qLeft 6 (by
      have := (tag_cells x w htag).1; omega) := by
  rcases (FixedContentGammaTerminator.gamma_contract _).1 zeros hg with ⟨hlt, ht, hz⟩
  have hs : machine.run 1 (startConfig B x w) =
      cfg B x w qLeft (7 + zeros) (by omega) := by
    rw [UniformTM.run, start_some (B := B) x w hg]
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      step_start_true (B := B) x w (8 + zeros) hlt (by
        simpa [FixedContentTagGate.physicalSymbol, hlt] using ht)
  rw [show zeros + 2 = (1 + zeros) + 1 by omega, machine.run_add,
    show machine.run (1 + zeros) (startConfig B x w) = cfg B x w qLeft 7 (by omega) by
      rw [machine.run_add, hs, run_left_zeros x w hlt hz], UniformTM.run]
  apply step_left_false
  have hp := (tag_cells x w htag).2.2
  simpa [FixedContentTagGate.physicalSymbol, show 7 < a + m by omega] using hp

private theorem run_return {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    {zeros : Nat} (hlt : 8 + zeros < a + m)
    (hz : forall i, i < zeros ->
      FixedContentTagGate.physicalSymbol (Fin.append x w) (8 + i) = some false) :
    machine.run zeros (cfg B x w qReturn 8
      (by omega)
      (markedTape B x w)) =
      cfg B x w qReturn (8 + zeros) (Nat.le_of_lt hlt) (markedTape B x w) := by
  induction zeros with
  | zero => rfl
  | succ zeros ih =>
      rw [UniformTM.run, ih (by omega) (fun i hi => hz i (by omega))]
      apply step_return_false
      · omega
      · have hp := hz zeros (by omega)
        simpa [FixedContentTagGate.physicalSymbol, show 8 + zeros < a + m by
          omega]
          using hp

theorem handoff_exact {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true) :
    let p := FixedContentGammaTerminator.machine.run
      (FixedContentGammaTerminator.deadline a m)
      (FixedContentGammaTerminator.startConfig B x w)
    let c := startConfig B x w
    p = FixedContentGammaTerminator.finalConfig B x w ∧ c = retag p ∧
    c.state = machine.start ∧ c.head = p.head ∧ c.tape = p.tape := by
  dsimp
  rw [FixedContentGammaTerminator.run_deadline x w htag]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem run_success_exact {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    {zeros : Nat} (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros) :
    machine.run (successTime zeros) (startConfig B x w) = finalConfig B x w := by
  rcases tag_cells x w htag with ⟨hL, h6, h7⟩
  have gs := (FixedContentGammaTerminator.gamma_contract _).1 zeros hg
  have h6' : (Fin.append x w) ⟨6, by omega⟩ = true := by
    simpa [FixedContentTagGate.physicalSymbol, show 6 < a + m by omega] using h6
  have h7' : (Fin.append x w) ⟨7, by omega⟩ = false := by
    simpa [FixedContentTagGate.physicalSymbol, show 7 < a + m by omega] using h7
  have ht' : (Fin.append x w) ⟨8 + zeros, gs.1⟩ = true := by
    simpa [FixedContentTagGate.physicalSymbol, gs.1] using gs.2.1
  have hA := run_left (B := B) x w htag hg
  have hB := step_left_true (B := B) x w hL h6'
  have hC := step_erase (B := B) x w hL h7'
  have hD := run_return (B := B) x w gs.1 gs.2.2
  have hE := step_return_true (B := B) x w (8 + zeros) gs.1 (by omega) ht'
  have hB' : machine.run 1 (cfg B x w qLeft 6 (by omega)) =
      cfg B x w qErase 7 (by omega) := by simpa [UniformTM.run] using hB
  have hC' : machine.run 1 (cfg B x w qErase 7 (by omega)) =
      cfg B x w qReturn 8 (by omega) (markedTape B x w) := by
    simpa [UniformTM.run] using hC
  have hE' : machine.run 1
      (cfg B x w qReturn (8 + zeros) (Nat.le_of_lt gs.1) (markedTape B x w)) =
      cfg B x w qAccept (8 + zeros) (Nat.le_of_lt gs.1) (markedTape B x w) := by
    simpa [UniformTM.run] using hE
  rw [show successTime zeros = (zeros + 2) + (1 + 1 + zeros + 1) by
    simp [successTime]; omega, machine.run_add, hA,
    show 1 + 1 + zeros + 1 = 1 + (1 + (zeros + 1)) by omega,
    machine.run_add, hB', machine.run_add, hC', machine.run_add, hD, hE']
  simp [finalConfig, hg, cfg, FixedContentGammaTerminator.terminalIndex,
    Nat.min_eq_left (Nat.le_of_lt gs.1)]

theorem run_reject_exact {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = none) :
    machine.run 1 (startConfig B x w) = finalConfig B x w := by
  rw [UniformTM.run, start_none (B := B) x w hg]
  have hr := base_blank (B := B) x w
  rw [step_keep _ qReject none .stay (by simpa [cfg] using hr) start_blank_action]
  apply config_ext
  · simp [finalConfig, hg]
  · apply Fin.ext; simp [finalConfig, hg, cfg, UniformTM.run,
      FixedContentGammaTerminator.terminalIndex, moveHead]
  · simp [finalConfig, hg, cfg, baseTape, UniformTM.run]

theorem successTime_le_deadline {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    {zeros : Nat} (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros) :
    successTime zeros ≤ deadline a m := by
  have h := ((FixedContentGammaTerminator.gamma_contract _).1 zeros hg).1
  change 2 * zeros + 5 ≤ 2 * (a + m)
  omega

theorem run_deadline {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true) :
    machine.run (deadline a m) (startConfig B x w) = finalConfig B x w := by
  cases hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) with
  | some zeros =>
      rw [show deadline a m = successTime zeros + (deadline a m - successTime zeros) by
        have := successTime_le_deadline x w hg; omega,
        machine.run_add, run_success_exact x w htag hg]
      apply machine.run_accept
      simp [finalConfig, hg, machine]
  | none =>
      have hL := (tag_cells x w htag).1
      rw [show deadline a m = 1 + (deadline a m - 1) by unfold deadline; omega,
        machine.run_add, run_reject_exact (B := B) x w hg]
      apply machine.run_reject
      simp [finalConfig, hg, machine]

theorem exact_terminal_contract {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true) :
    (forall zeros, FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros →
      (∀ s < successTime zeros,
        (machine.run s (startConfig B x w)).state ≠ machine.accept ∧
        (machine.run s (startConfig B x w)).state ≠ machine.reject) ∧
      machine.run (successTime zeros) (startConfig B x w) = finalConfig B x w ∧
      successTime zeros ≤ deadline a m) ∧
    (FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = none →
      (∀ s < 1, (machine.run s (startConfig B x w)).state ≠ machine.accept ∧
        (machine.run s (startConfig B x w)).state ≠ machine.reject) ∧
      machine.run 1 (startConfig B x w) = finalConfig B x w) := by
  constructor
  · intro zeros hg
    rcases tag_cells x w htag with ⟨hL, h6, h7⟩
    rcases (FixedContentGammaTerminator.gamma_contract _).1 zeros hg with ⟨hlt, ht, hz⟩
    have h6' : (Fin.append x w) ⟨6, by omega⟩ = true := by
      simpa [FixedContentTagGate.physicalSymbol, show 6 < a + m by omega] using h6
    have h7' : (Fin.append x w) ⟨7, by omega⟩ = false := by
      simpa [FixedContentTagGate.physicalSymbol, show 7 < a + m by omega] using h7
    have hA := run_left (B := B) x w htag hg
    have hB : machine.run 1 (cfg B x w qLeft 6 (by omega)) =
        cfg B x w qErase 7 (by omega) := by
      simpa [UniformTM.run] using step_left_true (B := B) x w hL h6'
    have hC : machine.run 1 (cfg B x w qErase 7 (by omega)) =
        cfg B x w qReturn 8 (by omega) (markedTape B x w) := by
      simpa [UniformTM.run] using step_erase (B := B) x w hL h7'
    have hABC : machine.run (zeros + 4) (startConfig B x w) =
        cfg B x w qReturn 8 (by omega) (markedTape B x w) := by
      rw [show zeros + 4 = (zeros + 2) + 1 + 1 by omega,
        machine.run_add, machine.run_add, hA, hB, hC]
    refine ⟨?_, run_success_exact x w htag hg, successTime_le_deadline x w hg⟩
    intro s hs
    by_cases hs0 : s = 0
    · subst s
      change qStart ≠ qAccept ∧ qStart ≠ qReject
      decide
    by_cases hsleft : s < zeros + 2
    · rw [run_success_pre_left (B := B) x w hg (by omega) hsleft]
      change qLeft ≠ qAccept ∧ qLeft ≠ qReject
      decide
    by_cases hsA : s = zeros + 2
    · subst s; rw [hA]
      change qLeft ≠ qAccept ∧ qLeft ≠ qReject
      decide
    by_cases hsB : s = zeros + 3
    · subst s
      rw [show zeros + 3 = (zeros + 2) + 1 by omega, machine.run_add, hA, hB]
      change qErase ≠ qAccept ∧ qErase ≠ qReject
      decide
    · have hr : s - (zeros + 4) ≤ zeros := by simp [successTime] at hs; omega
      rw [show s = (zeros + 4) + (s - (zeros + 4)) by omega,
        machine.run_add, hABC,
        run_return (B := B) x w (zeros := s - (zeros + 4)) (by omega)
          (fun i hi => hz i (by omega))]
      change qReturn ≠ qAccept ∧ qReturn ≠ qReject
      decide
  · intro hg
    refine ⟨?_, run_reject_exact (B := B) x w hg⟩
    intro s hs
    have : s = 0 := by omega
    subst s
    change qStart ≠ qAccept ∧ qStart ≠ qReject
    decide

theorem final_tape_contract {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true) :
    let c := machine.run (deadline a m) (startConfig B x w)
    (FixedContentGammaTerminator.gammaZeros? (Fin.append x w)).isSome →
      c.tape = markedTape B x w ∧
      (forall i, i.val ≠ 7 → c.tape i = FixedPairContentMarkerErase.contentTape B x w i) ∧
      (forall i, i.val = 7 → c.tape i = none) ∧
      (forall i, a + m ≤ i.val → c.tape i = none) := by
  dsimp
  intro hs
  rw [run_deadline x w htag]
  cases hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) with
  | none => simp [hg] at hs
  | some zeros =>
      simp only [finalConfig, hg, Option.isSome, if_true]
      refine ⟨trivial, ?_, ?_, ?_⟩
      · intro i hi
        have hn : i.val ≠ 7 := by simpa using hi
        simp [markedTape, hn]
      · intro i hi
        simp [markedTape, hi]
      · intro i hi
        have hL := (tag_cells x w htag).1
        have hn : i.val ≠ 7 := by omega
        simp [markedTape, hn, FixedPairContentMarkerErase.contentTape,
          Nat.not_lt_of_ge hi]

/-- Every configuration through the common deadline stays in the physical
input interval, so neither directional move is clamped.  Throughout the run,
only cell 7 may differ from the incoming content tape, and the suffix remains
blank. -/
theorem execution_safety {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true) :
    (∀ B s, s ≤ deadline a m →
      let c := machine.run s (startConfig B x w)
      6 ≤ c.head.val ∧ c.head.val ≤ a + m ∧
      (∀ i, i.val ≠ 7 →
        c.tape i = FixedPairContentMarkerErase.contentTape B x w i) ∧
      (∀ i, a + m ≤ i.val → c.tape i = none)) ∧
    (∀ B s, s < deadline a m →
      let c := machine.run s (startConfig B x w)
      let move := (machine.step c.state (c.tape c.head)).2.2
      (move = .left → 0 < c.head.val) ∧
      (move = .right → c.head.val + 1 < tapeLength (pairLength a m) B)) := by
  have hL := (tag_cells x w htag).1
  have base_props : ∀ B (i : Fin (tapeLength (pairLength a m) B)),
      (i.val ≠ 7 → baseTape B x w i = FixedPairContentMarkerErase.contentTape B x w i) ∧
      (a + m ≤ i.val → baseTape B x w i = none) := by
    intro B i
    exact ⟨fun _ => rfl, fun hi => by
      simp [baseTape, FixedPairContentMarkerErase.contentTape, Nat.not_lt_of_ge hi]⟩
  have marked_props : ∀ B (i : Fin (tapeLength (pairLength a m) B)),
      (i.val ≠ 7 → markedTape B x w i = FixedPairContentMarkerErase.contentTape B x w i) ∧
      (a + m ≤ i.val → markedTape B x w i = none) := by
    intro B i
    constructor
    · intro hi; simp [markedTape, hi]
    · intro hi
      have hi7 : i.val ≠ 7 := by omega
      simp [markedTape, hi7, FixedPairContentMarkerErase.contentTape, Nat.not_lt_of_ge hi]
  have shape : ∀ B s, s ≤ deadline a m →
      let c := machine.run s (startConfig B x w)
      (6 ≤ c.head.val ∧ c.head.val ≤ a + m ∧ c.tape = baseTape B x w) ∨
      (7 ≤ c.head.val ∧ c.head.val ≤ a + m ∧ c.tape = markedTape B x w) := by
    intro B s hs
    cases hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) with
    | none =>
        by_cases hs0 : s = 0
        · subst s
          left
          rw [start_none (B := B) x w hg]
          change 6 ≤ a + m ∧ a + m ≤ a + m ∧ _
          exact ⟨by omega, le_rfl, rfl⟩
        · left
          rw [show s = 1 + (s - 1) by omega, machine.run_add,
            run_reject_exact (B := B) x w hg]
          rw [machine.run_reject (finalConfig B x w) (by simp [finalConfig, hg, machine])]
          change 6 ≤ (finalConfig B x w).head.val ∧
            (finalConfig B x w).head.val ≤ a + m ∧
            (finalConfig B x w).tape = baseTape B x w
          simp [finalConfig, hg, FixedContentGammaTerminator.terminalIndex, baseTape]
          omega
    | some zeros =>
        rcases (FixedContentGammaTerminator.gamma_contract _).1 zeros hg with ⟨hlt, ht, hz⟩
        by_cases hpost : successTime zeros ≤ s
        · right
          rw [show s = successTime zeros + (s - successTime zeros) by omega,
            machine.run_add, run_success_exact x w htag hg]
          rw [machine.run_accept (finalConfig B x w) (by simp [finalConfig, hg, machine])]
          change 7 ≤ (finalConfig B x w).head.val ∧
            (finalConfig B x w).head.val ≤ a + m ∧
            (finalConfig B x w).tape = markedTape B x w
          simp [finalConfig, hg, FixedContentGammaTerminator.terminalIndex,
            Nat.min_eq_left (Nat.le_of_lt hlt)]
          omega
        · have hpre : s < successTime zeros := by omega
          by_cases hs0 : s = 0
          · subst s
            left
            rw [start_some (B := B) x w hg]
            change 6 ≤ 8 + zeros ∧ 8 + zeros ≤ a + m ∧ _
            exact ⟨by omega, by omega, rfl⟩
          by_cases hsleft : s < zeros + 2
          · left
            rw [run_success_pre_left (B := B) x w hg (by omega) hsleft]
            change 6 ≤ 8 + zeros - s ∧ 8 + zeros - s ≤ a + m ∧ _
            exact ⟨by omega, by omega, rfl⟩
          have hA := run_left (B := B) x w htag hg
          by_cases hsA : s = zeros + 2
          · subst s; left; rw [hA]
            change 6 ≤ 6 ∧ 6 ≤ a + m ∧ _
            exact ⟨le_rfl, by omega, rfl⟩
          have h6 := (tag_cells x w htag).2.1
          have h6' : (Fin.append x w) ⟨6, by omega⟩ = true := by
            simpa [FixedContentTagGate.physicalSymbol, show 6 < a + m by omega] using h6
          have hB : machine.run 1 (cfg B x w qLeft 6 (by omega)) =
              cfg B x w qErase 7 (by omega) := by
            simpa [UniformTM.run] using step_left_true (B := B) x w hL h6'
          by_cases hsB : s = zeros + 3
          · subst s; left
            rw [show zeros + 3 = (zeros + 2) + 1 by omega, machine.run_add, hA, hB]
            change 6 ≤ 7 ∧ 7 ≤ a + m ∧ _
            exact ⟨by omega, by omega, rfl⟩
          have h7 := (tag_cells x w htag).2.2
          have h7' : (Fin.append x w) ⟨7, by omega⟩ = false := by
            simpa [FixedContentTagGate.physicalSymbol, show 7 < a + m by omega] using h7
          have hC : machine.run 1 (cfg B x w qErase 7 (by omega)) =
              cfg B x w qReturn 8 (by omega) (markedTape B x w) := by
            simpa [UniformTM.run] using step_erase (B := B) x w hL h7'
          have hABC : machine.run (zeros + 4) (startConfig B x w) =
              cfg B x w qReturn 8 (by omega) (markedTape B x w) := by
            rw [show zeros + 4 = (zeros + 2) + 1 + 1 by omega,
              machine.run_add, machine.run_add, hA, hB, hC]
          have hrz : s - (zeros + 4) ≤ zeros := by
            simp [successTime] at hpre
            omega
          right
          rw [show s = (zeros + 4) + (s - (zeros + 4)) by omega,
            machine.run_add, hABC,
            run_return (B := B) x w (zeros := s - (zeros + 4)) (by omega)
              (fun i hi => hz i (by simp [successTime] at hpre; omega))]
          change 7 ≤ 8 + (s - (zeros + 4)) ∧
            8 + (s - (zeros + 4)) ≤ a + m ∧ _
          exact ⟨by omega, by
            have : s - (zeros + 4) ≤ zeros := by simp [successTime] at hpre; omega
            omega, rfl⟩
  constructor
  · intro B s hs
    rcases shape B s hs with hbase | hmarked
    · refine ⟨hbase.1, hbase.2.1, ?_, ?_⟩
      · intro i hi; rw [hbase.2.2]; exact (base_props B i).1 hi
      · intro i hi; rw [hbase.2.2]; exact (base_props B i).2 hi
    · refine ⟨by omega, hmarked.2.1, ?_, ?_⟩
      · intro i hi; rw [hmarked.2.2]; exact (marked_props B i).1 hi
      · intro i hi; rw [hmarked.2.2]; exact (marked_props B i).2 hi
  · intro B s hs
    dsimp
    have hb := (shape B s (Nat.le_of_lt hs))
    constructor
    · intro _
      rcases hb with hb | hb <;> omega
    · intro _
      rcases hb with hb | hb
      · unfold tapeLength pairLength
        omega
      · unfold tapeLength pairLength
        omega

/-- At every common time, executions with different tape budgets have the
same control, head value, and tape symbols at cells sharing a physical index. -/
theorem budget_independence_through_deadline {a m : Nat}
    (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true) :
    ∀ B B' s, s ≤ deadline a m →
      let c := machine.run s (startConfig B x w)
      let c' := machine.run s (startConfig B' x w)
      c.state = c'.state ∧ c.head.val = c'.head.val ∧
      ∀ (i : Fin (tapeLength (pairLength a m) B))
        (i' : Fin (tapeLength (pairLength a m) B')),
        i.val = i'.val → c.tape i = c'.tape i' := by
  intro B B' s hs
  induction s with
  | zero =>
      simp only [UniformTM.run]
      refine ⟨rfl, rfl, ?_⟩
      intro i i' hi
      change FixedPairContentMarkerErase.contentTape B x w i =
        FixedPairContentMarkerErase.contentTape B' x w i'
      simp [FixedPairContentMarkerErase.contentTape, hi]
  | succ s ih =>
      have hs' : s ≤ deadline a m := by omega
      rcases ih hs' with ⟨hst, hhd, htp⟩
      have hsafe := (execution_safety x w htag).1
      have hb := hsafe B s hs'
      have hb' := hsafe B' s hs'
      simp only [UniformTM.run]
      apply And.intro
      · change (machine.step _ _).1 = (machine.step _ _).1
        rw [hst, htp _ _ (by exact hhd)]
      apply And.intro
      · change (moveHead _ (machine.step _ _).2.2).val =
          (moveHead _ (machine.step _ _).2.2).val
        rw [hst, htp _ _ (by exact hhd)]
        cases hm : (machine.step
          (machine.run s (startConfig B' x w)).state
          ((machine.run s (startConfig B' x w)).tape
            (machine.run s (startConfig B' x w)).head)).2.2
        · simp only [moveHead]
          omega
        · exact hhd
        · have hr : (machine.run s (startConfig B x w)).head.val + 1 <
              tapeLength (pairLength a m) B := by unfold tapeLength pairLength; omega
          have hr' : (machine.run s (startConfig B' x w)).head.val + 1 <
              tapeLength (pairLength a m) B' := by unfold tapeLength pairLength; omega
          simp only [moveHead]
          rw [dif_pos hr, dif_pos hr']
          exact congrArg (fun n => n + 1) hhd
      · intro i i' hi
        change (if i = _ then _ else _) = (if i' = _ then _ else _)
        have heqhead : (i = (machine.run s (startConfig B x w)).head) ↔
            (i' = (machine.run s (startConfig B' x w)).head) := by
          constructor <;> intro h
          · apply Fin.ext
            calc i'.val = i.val := hi.symm
              _ = (machine.run s (startConfig B x w)).head.val := by rw [h]
              _ = (machine.run s (startConfig B' x w)).head.val := hhd
          · apply Fin.ext
            calc i.val = i'.val := hi
              _ = (machine.run s (startConfig B' x w)).head.val := by rw [h]
              _ = (machine.run s (startConfig B x w)).head.val := hhd.symm
        by_cases hcell : i = (machine.run s (startConfig B x w)).head
        · have hcell' := heqhead.mp hcell
          simp [hcell, hcell', hst, htp _ _ hhd]
        · have hcell' : i' ≠ (machine.run s (startConfig B' x w)).head :=
            fun h => hcell (heqhead.mpr h)
          simp [hcell, hcell', htp i i' hi]

theorem phase_contract {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true) :
    (forall B, machine.run (deadline a m) (startConfig B x w) = finalConfig B x w) ∧
    (forall B, (machine.run (deadline a m) (startConfig B x w)).head.val ≤ a + m) ∧
    (forall B extra, machine.run (deadline a m + extra) (startConfig B x w) = finalConfig B x w) ∧
    (forall B B',
      (machine.run (deadline a m) (startConfig B x w)).state =
        (machine.run (deadline a m) (startConfig B' x w)).state ∧
      (machine.run (deadline a m) (startConfig B x w)).head.val =
        (machine.run (deadline a m) (startConfig B' x w)).head.val) ∧
    (∀ B s, s ≤ deadline a m →
      let c := machine.run s (startConfig B x w)
      6 ≤ c.head.val ∧ c.head.val ≤ a + m ∧
      (∀ i, i.val ≠ 7 → c.tape i = FixedPairContentMarkerErase.contentTape B x w i) ∧
      (∀ i, a + m ≤ i.val → c.tape i = none)) ∧
    (∀ B B' s, s ≤ deadline a m →
      let c := machine.run s (startConfig B x w)
      let c' := machine.run s (startConfig B' x w)
      c.state = c'.state ∧ c.head.val = c'.head.val ∧
      ∀ (i : Fin (tapeLength (pairLength a m) B))
        (i' : Fin (tapeLength (pairLength a m) B')), i.val = i'.val → c.tape i = c'.tape i') := by
  refine ⟨fun B => run_deadline x w htag, ?_, ?_, ?_,
    (execution_safety x w htag).1, budget_independence_through_deadline x w htag⟩
  · intro B; rw [run_deadline x w htag]; simp [finalConfig]
  · intro B extra
    rw [machine.run_add, run_deadline x w htag]
    cases hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) with
    | some zeros => apply machine.run_accept; simp [finalConfig, hg, machine]
    | none => apply machine.run_reject; simp [finalConfig, hg, machine]
  · intro B B'; rw [run_deadline x w htag, run_deadline x w htag]
    simp [finalConfig]

end Pnp3.Complexity.Uniform.V1.FixedContentGammaAnchor
