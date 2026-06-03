import Pnp4.Frontier.ContractExpansion.TreeMCSPScanRightOneProgram
import Pnp4.Frontier.ContractExpansion.TreeMCSPGateRecordLayout

/-!
# Tape-level unary-field reader (NP-verifier track — decoder brick D1a)

The atomic step of the on-tape gate decoder/interpreter (`TM_VERIFIER_STRATEGY.md` §6k): reading one
**unary field** `1^len 0` off the tape.  Every field of a gate record (the tag, the input index, each
back-reference distance) is a unary field, so this one primitive is reused throughout.

The *motion* is `selfLoopScanRightOne` (scan right over `1`s, stop on the `0` terminator); this file
adds the **reader-framed** correctness — it advances exactly `len` cells over a `1^len 0` field — and
the **bridge to the D0 spec**: the bits it scans, read off the tape as a `List Bool` (`tapeReadList`),
are exactly `unaryField len`, and `decodeUnaryField` recovers `len`.  So the tape primitive realises the
pure spec proved in `TreeMCSPGateRecordLayout`.

Scope (D1a): the unary-field reader only.  *Not* here: the one-gate-record decoder (D1b), the
witness→record-stream decoder (D2), the interpreter, the row loop, or any assembly.
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-! ### Reading the tape contents as a `List Bool` -/

/-- `tapeReadList c h len` is the list of the `len` tape cells starting at offset `h` (out-of-range
cells read as the blank `false`).  The pure-list view of a tape segment, used to bridge tape behaviour
to the `List Bool` spec in `TreeMCSPGateRecordLayout`. -/
def tapeReadList {M : TM} {L : Nat} (c : Configuration (M := M) L) : Nat → Nat → List Bool
  | _, 0 => []
  | h, (len + 1) =>
      (if hp : h < M.tapeLength L then c.tape ⟨h, hp⟩ else false) :: tapeReadList c (h + 1) len

/-- One-step unfolding of `tapeReadList` (the cons case), for controlled rewriting (avoids the
recursive over-unfolding `simp [tapeReadList]` would do). -/
theorem tapeReadList_succ {M : TM} {L : Nat} (c : Configuration (M := M) L) (h len : Nat) :
    tapeReadList c h (len + 1)
      = (if hp : h < M.tapeLength L then c.tape ⟨h, hp⟩ else false) :: tapeReadList c (h + 1) len :=
  rfl

/-- **Bridge to the spec**: a tape segment that holds a `1^len 0` field (the `len` cells from `h` are
`true`, cell `h + len` is `false`) reads off as exactly `unaryField len`. -/
theorem tapeReadList_eq_unaryField {M : TM} {L : Nat} (c : Configuration (M := M) L)
    (h len : Nat) (hb : h + len < M.tapeLength L)
    (hones : ∀ p : Fin (M.tapeLength L), h ≤ (p : Nat) → (p : Nat) < h + len → c.tape p = true)
    (hterm : ∀ p : Fin (M.tapeLength L), (p : Nat) = h + len → c.tape p = false) :
    tapeReadList c h (len + 1) = unaryField len := by
  induction len generalizing h with
  | zero =>
      have hpb : h < M.tapeLength L := by omega
      have hv : (⟨h, hpb⟩ : Fin (M.tapeLength L)).val = h := rfl
      have hbit : c.tape ⟨h, hpb⟩ = false := hterm ⟨h, hpb⟩ (by omega)
      rw [tapeReadList_succ, dif_pos hpb, hbit]
      simp [tapeReadList, unaryField]
  | succ len ih =>
      have hpb : h < M.tapeLength L := by omega
      have hv : (⟨h, hpb⟩ : Fin (M.tapeLength L)).val = h := rfl
      have hbit : c.tape ⟨h, hpb⟩ = true := hones ⟨h, hpb⟩ (by omega) (by omega)
      have hih : tapeReadList c (h + 1) (len + 1) = unaryField len :=
        ih (h + 1) (by omega)
          (fun p hp1 hp2 => hones p (by omega) (by omega))
          (fun p hpe => hterm p (by omega))
      rw [tapeReadList_succ, dif_pos hpb, hbit, hih]
      simp [unaryField, List.replicate_succ]

/-! ### Reader correctness (standalone) -/

/-- Reading a `1^len 0` unary field at the head: after `len + 1` steps the machine has scanned the `len`
ones and stopped on the `0` terminator (done phase `1`), with the head advanced exactly `len` cells and
the tape unchanged.  The reader-framed specialisation of `selfLoopScanRightOne_runConfig_terminator`
(terminator at `head + len`). -/
theorem selfLoopScanRightOne_readsUnaryField {L : Nat}
    (c0 : Configuration (M := selfLoopScanRightOne.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 0) (len : Nat)
    (hb : (c0.head : Nat) + len < selfLoopScanRightOne.toPhased.toTM.tapeLength L)
    (hones : ∀ p : Fin (selfLoopScanRightOne.toPhased.toTM.tapeLength L),
      (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + len → c0.tape p = true)
    (hterm : ∀ p : Fin (selfLoopScanRightOne.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + len → c0.tape p = false) :
    (((TM.runConfig (M := selfLoopScanRightOne.toPhased.toTM) c0 (len + 1)).state).fst : Nat) = 1
      ∧ ((TM.runConfig (M := selfLoopScanRightOne.toPhased.toTM) c0 (len + 1)).head : Nat)
          = (c0.head : Nat) + len
      ∧ (TM.runConfig (M := selfLoopScanRightOne.toPhased.toTM) c0 (len + 1)).tape = c0.tape := by
  have h := selfLoopScanRightOne_runConfig_terminator c0 hphase ((c0.head : Nat) + len)
    (Nat.le_add_right _ _) hb hones hterm
  have he : (c0.head : Nat) + len - (c0.head : Nat) = len := by omega
  rw [he] at h
  exact h

/-- **Spec bridge for the reader**: the bits the reader scans (the `len + 1` cells from the head, read
off as a `List Bool`) decode, via the D0 spec `decodeUnaryField`, to exactly `len` — tying the tape
primitive's behaviour to the pure codec. -/
theorem decodeUnaryField_tapeReadList_of_reads {L : Nat}
    (c0 : Configuration (M := selfLoopScanRightOne.toPhased.toTM) L)
    (len : Nat)
    (hb : (c0.head : Nat) + len < selfLoopScanRightOne.toPhased.toTM.tapeLength L)
    (hones : ∀ p : Fin (selfLoopScanRightOne.toPhased.toTM.tapeLength L),
      (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + len → c0.tape p = true)
    (hterm : ∀ p : Fin (selfLoopScanRightOne.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + len → c0.tape p = false) :
    decodeUnaryField (tapeReadList c0 (c0.head : Nat) (len + 1)) = some (len, []) := by
  rw [tapeReadList_eq_unaryField c0 (c0.head : Nat) len hb hones hterm]
  simpa using decodeUnaryField_unaryField len []

/-! ### Reader correctness as a non-first (P2-region) phase -/

/-- The reader as a non-first phase of a `seq` (composition phase `P1.numPhases`): reads a `1^len 0`
field, advancing the head `len` cells and stopping at the shifted done phase `P1.numPhases + 1`.  The
reader-framed specialisation of `selfLoopScanRightOne_seqP2_runConfig_terminator`. -/
theorem selfLoopScanRightOne_readsUnaryField_seqP2 (P1 : ConstStatePhasedProgram Unit) {L : Nat}
    (c0 : Configuration (M := (seq P1 selfLoopScanRightOne).toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = P1.numPhases) (len : Nat)
    (hb : (c0.head : Nat) + len < (seq P1 selfLoopScanRightOne).toPhased.toTM.tapeLength L)
    (hones : ∀ p : Fin ((seq P1 selfLoopScanRightOne).toPhased.toTM.tapeLength L),
      (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + len → c0.tape p = true)
    (hterm : ∀ p : Fin ((seq P1 selfLoopScanRightOne).toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + len → c0.tape p = false) :
    (((TM.runConfig (M := (seq P1 selfLoopScanRightOne).toPhased.toTM) c0 (len + 1)).state).fst : Nat)
        = P1.numPhases + 1
      ∧ ((TM.runConfig (M := (seq P1 selfLoopScanRightOne).toPhased.toTM) c0 (len + 1)).head : Nat)
          = (c0.head : Nat) + len
      ∧ (TM.runConfig (M := (seq P1 selfLoopScanRightOne).toPhased.toTM) c0 (len + 1)).tape
          = c0.tape := by
  have h := selfLoopScanRightOne_seqP2_runConfig_terminator P1 c0 hphase ((c0.head : Nat) + len)
    (Nat.le_add_right _ _) hb hones hterm
  have he : (c0.head : Nat) + len - (c0.head : Nat) = len := by omega
  rw [he] at h
  exact h

end ContractExpansion
end Frontier
end Pnp4
