import Complexity.Uniform.V1.FixedGammaPayloadPendingCleanup
import Complexity.Uniform.V1.FixedGammaPayloadZeroCleanup
import Mathlib.Data.Fintype.Card

/-!
# Fixed gamma-payload dispatcher (Part A G2k)

This is the first executable unification of the G2 payload machines.  It starts
by retagging the *actual* deadline run of G2a, not a configuration computed from
`gammaZeros?`.  Its fixed table routes the cursor core into the repeated round,
the two pending cleanups, the exhausted cleanup, and three absorbing endpoints.

Only the malformed, zero-width, and first-read (`k = 0`) paths are activated by
run theorems in this slice.  The remaining table routes are executable but are
not claimed to have whole-dispatcher semantics here.  In particular `qHasOne`
is a distinct internal endpoint, not rejection or semantic acceptance.
-/

namespace Pnp3.Complexity.Uniform.V1.FixedGammaPayloadDispatcher

open PairEncoding

abbrev stateCount : Nat := 28

-- CursorCore work states (the four old exits are routed below).
def qCursorStart : Fin stateCount := ⟨0, by decide⟩
def qCursorBackFirst : Fin stateCount := ⟨1, by decide⟩
def qCursorBackSeen : Fin stateCount := ⟨2, by decide⟩
def qCursorSpend : Fin stateCount := ⟨3, by decide⟩
def qCursorSeekTerm : Fin stateCount := ⟨4, by decide⟩
def qCursorRead : Fin stateCount := ⟨5, by decide⟩
def qCursorRestoreOne : Fin stateCount := ⟨6, by decide⟩
def qCursorRestoreVirtual : Fin stateCount := ⟨7, by decide⟩
def qCursorFillOne : Fin stateCount := ⟨8, by decide⟩
def qCursorFillVirtual : Fin stateCount := ⟨9, by decide⟩

-- RoundStep work states.  A false read loops to qRoundStart.
def qRoundStart : Fin stateCount := ⟨10, by decide⟩
def qRoundBackPayload : Fin stateCount := ⟨11, by decide⟩
def qRoundBackCounter : Fin stateCount := ⟨12, by decide⟩
def qRoundSpend : Fin stateCount := ⟨13, by decide⟩
def qRoundSeekTerm : Fin stateCount := ⟨14, by decide⟩
def qRoundSeekHole : Fin stateCount := ⟨15, by decide⟩
def qRoundRead : Fin stateCount := ⟨16, by decide⟩

-- Exhausted/zero cleanup work states.
def qZeroScanRight : Fin stateCount := ⟨17, by decide⟩
def qZeroBackTerm : Fin stateCount := ⟨18, by decide⟩
def qZeroFillCounter : Fin stateCount := ⟨19, by decide⟩

-- Pending cleanup, including the symbol-dispatch state.
def qPendingStart : Fin stateCount := ⟨20, by decide⟩
def qPendingBackOne : Fin stateCount := ⟨21, by decide⟩
def qPendingBackVirtual : Fin stateCount := ⟨22, by decide⟩
def qPendingFillOne : Fin stateCount := ⟨23, by decide⟩
def qPendingFillVirtual : Fin stateCount := ⟨24, by decide⟩

def qAllZero : Fin stateCount := ⟨25, by decide⟩
def qHasOne : Fin stateCount := ⟨26, by decide⟩
def qReject : Fin stateCount := ⟨27, by decide⟩

/-- The complete fixed 28-state, 84-row dispatcher table. -/
def raw (q : Fin stateCount) (s : Option Bool) :
    Fin stateCount × Option Bool × Move :=
  match q.1 with
  | 0 => match s with
    | some true => (qCursorBackFirst, some true, .left)
    | s => (qReject, s, .stay)
  | 1 => match s with
    | some false => (qCursorBackSeen, some false, .left)
    | none => (qAllZero, some false, .stay)
    | s => (qReject, s, .stay)
  | 2 => match s with
    | some false => (qCursorBackSeen, some false, .left)
    | none => (qCursorSpend, none, .right)
    | s => (qReject, s, .stay)
  | 3 => match s with
    | some false => (qCursorSeekTerm, none, .right)
    | s => (qReject, s, .stay)
  | 4 => match s with
    | some false => (qCursorSeekTerm, some false, .right)
    | some true => (qCursorRead, some true, .right)
    | none => (qReject, none, .stay)
  | 5 => match s with
    | some false => (qRoundStart, none, .stay)
    | some true => (qCursorRestoreOne, some true, .left)
    | none => (qCursorRestoreVirtual, none, .left)
  | 6 => match s with
    | none => (qCursorFillOne, some false, .left)
    | s => (qCursorRestoreOne, s, .left)
  | 7 => match s with
    | none => (qCursorFillVirtual, some false, .left)
    | s => (qCursorRestoreVirtual, s, .left)
  | 8 => match s with
    | none => (qHasOne, some false, .left)
    | s => (qReject, s, .stay)
  | 9 => match s with
    | none => (qAllZero, some false, .left)
    | s => (qReject, s, .stay)
  | 10 => match s with
    | none => (qRoundBackPayload, none, .left)
    | s => (qReject, s, .stay)
  | 11 => match s with
    | some false => (qRoundBackPayload, some false, .left)
    | some true => (qRoundBackCounter, some true, .left)
    | none => (qReject, none, .stay)
  | 12 => match s with
    | some false => (qRoundBackCounter, some false, .left)
    | none => (qRoundSpend, none, .right)
    | some true => (qReject, some true, .stay)
  | 13 => match s with
    | some false => (qRoundSeekTerm, none, .right)
    | some true => (qZeroScanRight, some true, .stay)
    | none => (qReject, none, .stay)
  | 14 => match s with
    | some false => (qRoundSeekTerm, some false, .right)
    | some true => (qRoundSeekHole, some true, .right)
    | none => (qReject, none, .stay)
  | 15 => match s with
    | some false => (qRoundSeekHole, some false, .right)
    | none => (qRoundRead, some false, .right)
    | some true => (qReject, some true, .stay)
  | 16 => match s with
    | some false => (qRoundStart, none, .stay)
    | some true => (qPendingStart, some true, .stay)
    | none => (qPendingStart, none, .stay)
  | 17 => match s with
    | none => (qZeroBackTerm, some false, .left)
    | some b => (qZeroScanRight, some b, .right)
  | 18 => match s with
    | none => (qZeroFillCounter, some false, .left)
    | some b => (qZeroBackTerm, some b, .left)
  | 19 => match s with
    | none => (qZeroFillCounter, some false, .left)
    | some true => (qAllZero, some true, .stay)
    | some false => (qReject, some false, .stay)
  | 20 => match s with
    | some true => (qPendingBackOne, some true, .left)
    | none => (qPendingBackVirtual, none, .left)
    | some false => (qReject, some false, .stay)
  | 21 => match s with
    | none => (qPendingFillOne, some false, .left)
    | some b => (qPendingBackOne, some b, .left)
  | 22 => match s with
    | none => (qPendingFillVirtual, some false, .left)
    | some b => (qPendingBackVirtual, some b, .left)
  | 23 => match s with
    | none => (qPendingFillOne, some false, .left)
    | some true => (qHasOne, some true, .stay)
    | some false => (qReject, some false, .stay)
  | 24 => match s with
    | none => (qPendingFillVirtual, some false, .left)
    | some true => (qAllZero, some true, .stay)
    | some false => (qReject, some false, .stay)
  | 25 => (qAllZero, s, .stay)
  | 26 => (qHasOne, s, .stay)
  | _ => (qReject, s, .stay)

def machine : UniformTM where
  stateCount := stateCount
  start := qCursorStart
  accept := qAllZero
  reject := qReject
  accept_ne_reject := by decide
  rawStep := raw

/-- Honest input ABI: retag the actual G2a deadline execution. -/
def retagG2a {N B : Nat} (c : Config FixedContentGammaAnchor.stateCount N B) :
    Config stateCount N B := ⟨qCursorStart, c.head, c.tape⟩

def startConfig {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) :
    Config stateCount (pairLength a m) B :=
  retagG2a (FixedContentGammaAnchor.machine.run (FixedContentGammaAnchor.deadline a m)
    (FixedContentGammaAnchor.startConfig B x w))

theorem table_and_resource_pins :
    (∀ s, machine.step qCursorStart s = match s with
      | some true => (qCursorBackFirst, some true, .left) | s => (qReject, s, .stay)) ∧
    (∀ s, machine.step qCursorBackFirst s = match s with
      | some false => (qCursorBackSeen, some false, .left)
      | none => (qAllZero, some false, .stay) | s => (qReject, s, .stay)) ∧
    (∀ s, machine.step qCursorBackSeen s = match s with
      | some false => (qCursorBackSeen, some false, .left)
      | none => (qCursorSpend, none, .right) | s => (qReject, s, .stay)) ∧
    (∀ s, machine.step qCursorSpend s = match s with
      | some false => (qCursorSeekTerm, none, .right) | s => (qReject, s, .stay)) ∧
    (∀ s, machine.step qCursorSeekTerm s = match s with
      | some false => (qCursorSeekTerm, some false, .right)
      | some true => (qCursorRead, some true, .right) | none => (qReject, none, .stay)) ∧
    (∀ s, machine.step qCursorRead s = match s with
      | some false => (qRoundStart, none, .stay)
      | some true => (qCursorRestoreOne, some true, .left)
      | none => (qCursorRestoreVirtual, none, .left)) ∧
    (∀ s, machine.step qCursorRestoreOne s = match s with
      | none => (qCursorFillOne, some false, .left) | s => (qCursorRestoreOne, s, .left)) ∧
    (∀ s, machine.step qCursorRestoreVirtual s = match s with
      | none => (qCursorFillVirtual, some false, .left) | s => (qCursorRestoreVirtual, s, .left)) ∧
    (∀ s, machine.step qCursorFillOne s = match s with
      | none => (qHasOne, some false, .left) | s => (qReject, s, .stay)) ∧
    (∀ s, machine.step qCursorFillVirtual s = match s with
      | none => (qAllZero, some false, .left) | s => (qReject, s, .stay)) ∧
    (∀ s, machine.step qRoundStart s = match s with
      | none => (qRoundBackPayload, none, .left) | s => (qReject, s, .stay)) ∧
    (∀ s, machine.step qRoundBackPayload s = match s with
      | some false => (qRoundBackPayload, some false, .left)
      | some true => (qRoundBackCounter, some true, .left) | none => (qReject, none, .stay)) ∧
    (∀ s, machine.step qRoundBackCounter s = match s with
      | some false => (qRoundBackCounter, some false, .left)
      | none => (qRoundSpend, none, .right) | some true => (qReject, some true, .stay)) ∧
    (∀ s, machine.step qRoundSpend s = match s with
      | some false => (qRoundSeekTerm, none, .right)
      | some true => (qZeroScanRight, some true, .stay) | none => (qReject, none, .stay)) ∧
    (∀ s, machine.step qRoundSeekTerm s = match s with
      | some false => (qRoundSeekTerm, some false, .right)
      | some true => (qRoundSeekHole, some true, .right) | none => (qReject, none, .stay)) ∧
    (∀ s, machine.step qRoundSeekHole s = match s with
      | some false => (qRoundSeekHole, some false, .right)
      | none => (qRoundRead, some false, .right) | some true => (qReject, some true, .stay)) ∧
    (∀ s, machine.step qRoundRead s = match s with
      | some false => (qRoundStart, none, .stay)
      | some true => (qPendingStart, some true, .stay) | none => (qPendingStart, none, .stay)) ∧
    (∀ s, machine.step qZeroScanRight s = match s with
      | none => (qZeroBackTerm, some false, .left) | some b => (qZeroScanRight, some b, .right)) ∧
    (∀ s, machine.step qZeroBackTerm s = match s with
      | none => (qZeroFillCounter, some false, .left) | some b => (qZeroBackTerm, some b, .left)) ∧
    (∀ s, machine.step qZeroFillCounter s = match s with
      | none => (qZeroFillCounter, some false, .left)
      | some true => (qAllZero, some true, .stay) | some false => (qReject, some false, .stay)) ∧
    (∀ s, machine.step qPendingStart s = match s with
      | some true => (qPendingBackOne, some true, .left)
      | none => (qPendingBackVirtual, none, .left) | some false => (qReject, some false, .stay)) ∧
    (∀ s, machine.step qPendingBackOne s = match s with
      | none => (qPendingFillOne, some false, .left) | some b => (qPendingBackOne, some b, .left)) ∧
    (∀ s, machine.step qPendingBackVirtual s = match s with
      | none => (qPendingFillVirtual, some false, .left) | some b => (qPendingBackVirtual, some b, .left)) ∧
    (∀ s, machine.step qPendingFillOne s = match s with
      | none => (qPendingFillOne, some false, .left)
      | some true => (qHasOne, some true, .stay) | some false => (qReject, some false, .stay)) ∧
    (∀ s, machine.step qPendingFillVirtual s = match s with
      | none => (qPendingFillVirtual, some false, .left)
      | some true => (qAllZero, some true, .stay) | some false => (qReject, some false, .stay)) ∧
    (∀ s, machine.step qAllZero s = (qAllZero, s, .stay)) ∧
    (∀ s, machine.step qHasOne s = (qHasOne, s, .stay)) ∧
    (∀ s, machine.step qReject s = (qReject, s, .stay)) ∧
    machine.stateCount = 28 ∧ machine.start = qCursorStart ∧
    machine.accept = qAllZero ∧ machine.reject = qReject ∧
    qCursorStart.val = 0 ∧ qCursorBackFirst.val = 1 ∧ qCursorBackSeen.val = 2 ∧
    qCursorSpend.val = 3 ∧ qCursorSeekTerm.val = 4 ∧ qCursorRead.val = 5 ∧
    qCursorRestoreOne.val = 6 ∧ qCursorRestoreVirtual.val = 7 ∧
    qCursorFillOne.val = 8 ∧ qCursorFillVirtual.val = 9 ∧ qRoundStart.val = 10 ∧
    qRoundBackPayload.val = 11 ∧ qRoundBackCounter.val = 12 ∧ qRoundSpend.val = 13 ∧
    qRoundSeekTerm.val = 14 ∧ qRoundSeekHole.val = 15 ∧ qRoundRead.val = 16 ∧
    qZeroScanRight.val = 17 ∧ qZeroBackTerm.val = 18 ∧ qZeroFillCounter.val = 19 ∧
    qPendingStart.val = 20 ∧ qPendingBackOne.val = 21 ∧ qPendingBackVirtual.val = 22 ∧
    qPendingFillOne.val = 23 ∧ qPendingFillVirtual.val = 24 ∧
    qAllZero.val = 25 ∧ qHasOne.val = 26 ∧ qReject.val = 27 ∧
    Fintype.card (Fin machine.stateCount × Option Bool) = 84 := by
  repeat' apply And.intro
  all_goals first
    | (intro s; cases s with
       | none => decide
       | some b => cases b <;> decide)
    | decide

theorem handoff_exact {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let p := FixedContentGammaAnchor.machine.run (FixedContentGammaAnchor.deadline a m)
      (FixedContentGammaAnchor.startConfig B x w)
    let c := startConfig B x w
    c = retagG2a p ∧ c.state = machine.start ∧ c.head = p.head ∧ c.tape = p.tape := by
  exact ⟨rfl, rfl, rfl, rfl⟩

private def coreState (q : Fin FixedGammaPayloadCursorCore.stateCount) : Fin stateCount :=
  match q.val with
    | 0 => qCursorStart | 1 => qCursorBackFirst | 2 => qCursorBackSeen
    | 3 => qCursorSpend | 4 => qCursorSeekTerm | 5 => qCursorRead
    | 6 => qRoundStart | 7 => qCursorRestoreOne | 8 => qCursorRestoreVirtual
    | 9 => qCursorFillOne | 10 => qCursorFillVirtual | 11 => qHasOne
    | 12 => qAllZero | _ => qReject

private def embedCore {N B : Nat}
    (c : Config FixedGammaPayloadCursorCore.stateCount N B) : Config stateCount N B :=
  ⟨coreState c.state, c.head, c.tape⟩

private theorem action_embedCore
    (q : Fin FixedGammaPayloadCursorCore.stateCount) (s : Option Bool)
    (hnext : q ≠ FixedGammaPayloadCursorCore.qNextFalse) :
    machine.step (coreState q) s =
      (coreState (FixedGammaPayloadCursorCore.machine.step q s).1,
        (FixedGammaPayloadCursorCore.machine.step q s).2.1,
        (FixedGammaPayloadCursorCore.machine.step q s).2.2) := by
  rcases FixedGammaPayloadCursorCore.table_and_resource_pins with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, _⟩
  fin_cases q <;> try { exact (hnext rfl).elim } <;> cases s with
  | none => simp_all only [coreState]; all_goals decide
  | some b => cases b <;> simp_all only [coreState]; all_goals decide

private theorem config_ext {N B : Nat} {c d : Config stateCount N B}
    (hs : c.state = d.state) (hh : c.head = d.head) (ht : c.tape = d.tape) : c = d := by
  cases c; cases d; cases hs; cases hh; cases ht; rfl

private theorem step_embedCore {N B : Nat}
    (c : Config FixedGammaPayloadCursorCore.stateCount N B)
    (hnext : c.state ≠ FixedGammaPayloadCursorCore.qNextFalse) :
    machine.stepConfig (embedCore c) =
      embedCore (FixedGammaPayloadCursorCore.machine.stepConfig c) := by
  rcases c with ⟨q, head, tape⟩
  simp only [embedCore, UniformTM.stepConfig]
  rw [action_embedCore q (tape head) hnext]

private theorem core_run_embed_of_avoids {N B : Nat}
    (c : Config FixedGammaPayloadCursorCore.stateCount N B) (n : Nat)
    (havoid : ∀ i, i < n →
      (FixedGammaPayloadCursorCore.machine.run i c).state ≠
        FixedGammaPayloadCursorCore.qNextFalse) :
    machine.run n (embedCore c) =
      embedCore (FixedGammaPayloadCursorCore.machine.run n c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [UniformTM.run, UniformTM.run, ih (fun i hi => havoid i (by omega))]
      exact step_embedCore _ (havoid n (by omega))

private theorem core_next_absorbs {N B : Nat}
    (c : Config FixedGammaPayloadCursorCore.stateCount N B)
    (h : c.state = FixedGammaPayloadCursorCore.qNextFalse) (n : Nat) :
    FixedGammaPayloadCursorCore.machine.run n c = c := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [UniformTM.run, ih]
      rcases c with ⟨q, head, tape⟩
      have hrow := FixedGammaPayloadCursorCore.table_and_resource_pins.2.2.2.2.2.2.1
      simp_all [UniformTM.stepConfig, moveHead]
      funext i
      by_cases hi : i = head <;> simp [hi]

private theorem avoids_next_of_final {N B clock : Nat}
    (c : Config FixedGammaPayloadCursorCore.stateCount N B)
    (hfinal : (FixedGammaPayloadCursorCore.machine.run clock c).state ≠
      FixedGammaPayloadCursorCore.qNextFalse) :
    ∀ i, i < clock → (FixedGammaPayloadCursorCore.machine.run i c).state ≠
      FixedGammaPayloadCursorCore.qNextFalse := by
  intro i hi hnext
  have hdecomp : FixedGammaPayloadCursorCore.machine.run clock c =
      FixedGammaPayloadCursorCore.machine.run (clock - i)
        (FixedGammaPayloadCursorCore.machine.run i c) := by
    rw [← FixedGammaPayloadCursorCore.machine.run_add]
    congr 1
    omega
  rw [core_next_absorbs _ hnext] at hdecomp
  exact hfinal ((congrArg Config.state hdecomp).trans hnext)

private theorem actual_start_eq_core {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true) :
    startConfig B x w = embedCore (FixedGammaPayloadCursorCore.startConfig B x w) := by
  simp only [startConfig, FixedGammaPayloadCursorCore.startConfig]
  rw [FixedContentGammaAnchor.run_deadline x w htag]
  rfl

/-- Activated malformed path: shared reject in one dispatcher step. -/
theorem malformed_exact {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = none) :
    let d := machine.run 1 (startConfig B x w)
    d.state = qReject ∧ d.head.val = a + m ∧
      d.tape = FixedPairContentMarkerErase.contentTape B x w := by
  simp only [startConfig]
  rw [FixedContentGammaAnchor.run_deadline x w htag]
  have hb : FixedPairContentMarkerErase.contentTape B x w
      ⟨a + m, by unfold tapeLength pairLength; omega⟩ = none := by
    simp [FixedPairContentMarkerErase.contentTape]
  simp only [UniformTM.run, retagG2a, FixedContentGammaAnchor.finalConfig, hg,
    FixedContentGammaTerminator.terminalIndex]
  simp only [UniformTM.stepConfig]
  simp only [Option.isSome, Bool.false_eq_true, if_false, Nat.min_self]
  rw [hb]
  rw [show machine.step qCursorStart none = (qReject, none, .stay) by decide]
  simp [moveHead]
  funext i
  by_cases hi : i = ⟨a + m, by unfold tapeLength pairLength; omega⟩
  · subst i; simp [hb]
  · simp [hi]

/-- Activated zero-width path.  The branch preserves its historical head 7. -/
theorem zero_width_exact {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some 0) :
    machine.run 2 (startConfig B x w) =
      ⟨qAllZero, ⟨7, by
        have hs := ((FixedContentGammaTerminator.gamma_contract _).1 0 hg).1
        unfold tapeLength pairLength
        omega⟩, FixedPairContentMarkerErase.contentTape B x w⟩ := by
  rw [actual_start_eq_core x w htag]
  have hend := FixedGammaPayloadCursorCore.zero_width_exact (B := B) x w htag hg
  dsimp at hend
  rcases hend with ⟨hstate, hhead, htape⟩
  have hneq : (FixedGammaPayloadCursorCore.machine.run 2
      (FixedGammaPayloadCursorCore.startConfig B x w)).state ≠
      FixedGammaPayloadCursorCore.qNextFalse := by rw [hstate]; decide
  rw [core_run_embed_of_avoids _ 2 (avoids_next_of_final _ hneq)]
  apply config_ext
  · change coreState (FixedGammaPayloadCursorCore.machine.run 2
      (FixedGammaPayloadCursorCore.startConfig B x w)).state = qAllZero
    rw [hstate]
    decide
  · apply Fin.ext; exact hhead
  · exact htape

/-- Activated `k = 0` physical-true path, ending at the distinct internal endpoint. -/
theorem first_true_exact {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzero : 0 < zeros) (hp : 9 + zeros < a + m)
    (htrue : (Fin.append x w) ⟨9 + zeros, hp⟩ = true) :
    machine.run (3 * zeros + 6) (startConfig B x w) =
      ⟨qHasOne, ⟨6, by unfold tapeLength pairLength; omega⟩,
        FixedPairContentMarkerErase.contentTape B x w⟩ := by
  rw [actual_start_eq_core x w htag]
  have hend := FixedGammaPayloadCursorCore.first_physical_true_exact
    (B := B) x w htag hg hzero hp htrue
  have hneq : (FixedGammaPayloadCursorCore.machine.run (3 * zeros + 6)
      (FixedGammaPayloadCursorCore.startConfig B x w)).state ≠
      FixedGammaPayloadCursorCore.qNextFalse := by
    rw [hend]
    intro h
    have hv := congrArg Fin.val h
    norm_num [FixedGammaPayloadCursorCore.qOne,
      FixedGammaPayloadCursorCore.qNextFalse] at hv
  rw [core_run_embed_of_avoids _ _ (avoids_next_of_final _ hneq), hend]
  rfl

/-- Activated `k = 0` virtual path, with the cleaned head at 6. -/
theorem first_virtual_exact {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzero : 0 < zeros) (hvirtual : 9 + zeros = a + m) :
    machine.run (3 * zeros + 6) (startConfig B x w) =
      ⟨qAllZero, ⟨6, by unfold tapeLength pairLength; omega⟩,
        FixedPairContentMarkerErase.contentTape B x w⟩ := by
  rw [actual_start_eq_core x w htag]
  have hend := FixedGammaPayloadCursorCore.first_virtual_exact
    (B := B) x w htag hg hzero hvirtual
  have hneq : (FixedGammaPayloadCursorCore.machine.run (3 * zeros + 6)
      (FixedGammaPayloadCursorCore.startConfig B x w)).state ≠
      FixedGammaPayloadCursorCore.qNextFalse := by
    rw [hend]
    intro h
    have hv := congrArg Fin.val h
    norm_num [FixedGammaPayloadCursorCore.qVirtual,
      FixedGammaPayloadCursorCore.qNextFalse] at hv
  rw [core_run_embed_of_avoids _ _ (avoids_next_of_final _ hneq), hend]
  rfl

theorem endpoints_absorb {N B : Nat} (c : Config stateCount N B) :
    (c.state = qAllZero → ∀ n, machine.run n c = c) ∧
    (c.state = qHasOne → ∀ n, machine.run n c = c) ∧
    (c.state = qReject → ∀ n, machine.run n c = c) := by
  have absorb (q : Fin stateCount)
      (hrow : ∀ s, machine.step q s = (q, s, .stay))
      (h : c.state = q) (n : Nat) : machine.run n c = c := by
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [UniformTM.run, ih]
        rcases c with ⟨state, head, tape⟩
        change state = q at h
        subst state
        simp [UniformTM.stepConfig, hrow, moveHead]
        funext i
        by_cases hi : i = head <;> simp [hi]
  refine ⟨?_, ?_, ?_⟩
  · exact absorb qAllZero (fun s => by cases s with
      | none => decide
      | some b => cases b <;> decide)
  · exact absorb qHasOne (fun s => by cases s with
      | none => decide
      | some b => cases b <;> decide)
  · exact absorb qReject (fun s => by cases s with
      | none => decide
      | some b => cases b <;> decide)

theorem per_step_budget_independent : ∀ q s, machine.step q s = machine.rawStep q s :=
  by
    intro q s
    fin_cases q <;> cases s with
    | none => decide
    | some b => cases b <;> decide

end Pnp3.Complexity.Uniform.V1.FixedGammaPayloadDispatcher
