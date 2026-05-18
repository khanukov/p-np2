import Complexity.PsubsetPpolyInternal.TuringToolkit.Foundation
import Complexity.PsubsetPpolyInternal.TuringToolkit.AtomicPrograms
import Complexity.PsubsetPpolyInternal.TuringToolkit.ConstStatePhasedProgram
import Complexity.PsubsetPpolyInternal.TuringToolkit.BinaryCounter
import Models.Model_PartialMCSP
import Magnification.CanonicalAsymptoticTrackData
import Magnification.CanonicalAsymptoticDecider

/-!
# GapMCSP NP-verifier scaffold

This file lays out the structure for the canonical GapMCSP NP-verifier
TM required by
`Models.GapPartialMCSP_Asymptotic_TMWitness canonicalAsymptoticSpec`.

## Mathematical content (from Hitchcock; OPS19/CJW20)

For `canonicalAsymptoticSpec` with `sYES n = 1`, the language at canonical
input length `N = 2 · 2^n` accepts `x` iff:

  ∃ circuit C of size ≤ 1, consistent with `decodePartial x`.

Size-1 circuits over `n` variables are exactly:

  * `Circuit.const true`, `Circuit.const false` — 2 constants.
  * `Circuit.input i` for `i : Fin n` — `n` projections.

So there are `n + 2` candidates total.

A verifier `M : Internal.PsubsetPpoly.TM` with certificate `w` of length
`n^k + k` (we use `k = 2`, giving `n² + 2` bits) accepts `(x ++ w)` iff
`w` is a one-hot encoding of a size-1 circuit `C` that is consistent with
the decoded partial truth table.

## Verifier phases

The verifier is composed as a `PhasedProgram` chain with five phases:

  1. **Phase A — read certificate**:
     Walk right to the certificate region (positions `n .. n + certLen`),
     scan to find the unique `1` bit, save the candidate index in state.

  2. **Phase B — identify candidate**:
     From the candidate index, determine whether the candidate is
     `const true`, `const false`, or `input i` (for which `i`).

  3. **Phase C — walk table positions**:
     Initialize a counter `j = 0..2^n - 1` over table indices.  Use
     `BinaryCounter.incrementProgram` to advance `j`.

  4. **Phase D — check consistency**:
     For each `j`, read `mask[j]` (at position `j`) and `value[j]`
     (at position `2^n + j`).  If `mask[j] = true`, compare
     `value[j]` to the candidate's evaluation at `j` (interpreted as
     an `n`-bit assignment).  On mismatch, transition to reject phase.

  5. **Phase E — accept/reject**:
     After all `j` have been processed without mismatch, transition to
     accept.

## Runtime

Each phase runs in time polynomial in the input length:

  * Phase A: `O(certLen)` = `O(n²)`.
  * Phase B: `O(1)` (constant).
  * Phase C × D: `2^n` iterations, each `O(n + 1)` for navigation.
  * Total: `O(n · 2^n) = O(N · log N)` where `N = 2 · 2^n`.

So `runTime (n_total) ≤ (n_total)^c + c` for sufficiently large `c` (e.g.,
`c = 3`).

## Implementation status

This file currently provides the **interface scaffold**.  Each phase is
declared with its target signature; concrete `PhasedProgram` constructions
and correctness proofs are TODOs.  The estimated effort is ~800–1500 LOC.

The `TODO`-marked theorems are not proof-placeholder-bearing: they are simply not
yet defined.  The overall `canonicalGapMCSPVerifier` is also not yet a
definition; once each phase is built, it will be a single composition.

## Reduction target

The mathematical content has been **fully decomposed** in
`Magnification.CanonicalAsymptoticDecider`:

* `decideAsymptotic : (n : Nat) → Bitstring n → Bool` — a *computable*
  Boolean decider proved equivalent to
  `gapPartialMCSP_AsymptoticLanguage canonicalAsymptoticSpec`.
* `CanonicalAsymptoticVerifierComponents` — minimum-sufficient structure
  packaging a TM whose acceptance on `(x ++ w)` equals
  `decideAsymptotic n x` (independent of the certificate `w`).
* `CanonicalAsymptoticVerifierComponents.witness : Components →
  GapPartialMCSP_Asymptotic_TMWitness canonicalAsymptoticSpec`.

So the remaining open obligation is **just**:

```
buildCanonicalVerifierComponents :
  CanonicalAsymptoticVerifierComponents
```

i.e., a concrete TM realising `decideAsymptotic` in polynomial time.
Once this term exists, every `canonical_*` theorem in
`Tests/CanonicalIntegrationTests.lean` becomes unconditional.
-/

namespace Pnp3
namespace Internal
namespace PsubsetPpoly
namespace GapMCSPVerifier

open Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Models

/-! ## Verifier parameters

We fix `c := 3` for the runtime polynomial and `k := 2` for the certificate
length.  With `k = 2`, `certificateLength n 2 = n² + 2`, giving enough room
to encode a one-hot 1-of-(n+2) candidate via `n+2` certificate bits plus
slack.
-/

/-- Polynomial-runtime exponent: `runTime (n + cert) ≤ (n + cert)^3 + 3`. -/
def runtimeExponent : Nat := 3

/-- Certificate-length exponent: `certificateLength n k = n^k + k` with
`k = 2` gives `n^2 + 2` bits of certificate. -/
def certificateExponent : Nat := 2

/-! ## Phase A — certificate scan scaffold

Progress classification: **Infrastructure**.  This section is a local TM
engineering scaffold for the eventual verifier.  It does not perform any
lower-bound extraction, does not build a `ResearchGapWitness`, and does not
claim the final `CanonicalAsymptoticVerifierComponents` term.

The program below is intentionally small and honest: starting with the head at
the first certificate cell, it scans a fixed certificate window of length `L`,
records whether it has seen zero, exactly one, or multiple `1` bits, and then
enters a terminal handoff phase.  It does **not** claim full verifier
correctness; later sessions still have to connect this state to candidate
identification and row/table consistency.
-/

/-- Accumulator carried while scanning a one-hot certificate window.

* `none` means no `1` bit has been seen yet.
* `unique i` means the unique `1` seen so far was at certificate offset `i`.
* `many` means at least two `1` bits have been seen, so the one-hot check has
  already failed.
-/
inductive CertificateScanStatus (L : Nat) where
  | none : CertificateScanStatus L
  | unique : Fin L → CertificateScanStatus L
  | many : CertificateScanStatus L
  deriving DecidableEq, Repr, Fintype

namespace CertificateScanStatus

variable {L : Nat}

instance (L : Nat) : Inhabited (CertificateScanStatus L) :=
  ⟨CertificateScanStatus.none⟩

/-- Update the one-hot accumulator after reading certificate offset `i`.
A zero bit leaves the accumulator unchanged.  A one bit changes `none` to
`unique i`, but changes any previous `unique` or `many` state to `many`. -/
def register (s : CertificateScanStatus L) (i : Fin L) (bit : Bool) :
    CertificateScanStatus L :=
  if bit then
    match s with
    | CertificateScanStatus.none => CertificateScanStatus.unique i
    | CertificateScanStatus.unique _ => CertificateScanStatus.many
    | CertificateScanStatus.many => CertificateScanStatus.many
  else
    s

/-- Extract the candidate offset if and only if the scan has seen exactly one
`1` bit. -/
def candidate? : CertificateScanStatus L → Option (Fin L)
  | CertificateScanStatus.none => Option.none
  | CertificateScanStatus.unique i => some i
  | CertificateScanStatus.many => Option.none

@[simp] theorem register_false (s : CertificateScanStatus L) (i : Fin L) :
    register s i false = s := by
  simp [register]

@[simp] theorem register_none_true (i : Fin L) :
    register CertificateScanStatus.none i true = CertificateScanStatus.unique i := by
  simp [register]

@[simp] theorem register_unique_true (j i : Fin L) :
    register (CertificateScanStatus.unique j) i true = CertificateScanStatus.many := by
  simp [register]

@[simp] theorem register_many_true (i : Fin L) :
    register CertificateScanStatus.many i true = CertificateScanStatus.many := by
  simp [register]

@[simp] theorem candidate?_none :
    (CertificateScanStatus.none : CertificateScanStatus L).candidate? = Option.none := rfl

@[simp] theorem candidate?_unique (i : Fin L) :
    (CertificateScanStatus.unique i).candidate? = some i := rfl

@[simp] theorem candidate?_many :
    (CertificateScanStatus.many : CertificateScanStatus L).candidate? = Option.none := rfl

end CertificateScanStatus

/-- Fold-level specification of the certificate scan, independent of the TM
encoding.  The list is read left-to-right; offset `k` corresponds to the `k`th
certificate cell. -/
def scanCertificateStatus (L : Nat) (bits : List Bool) : CertificateScanStatus L :=
  ((List.finRange L).zip (bits.take L)).foldl
    (fun acc pair => CertificateScanStatus.register acc pair.fst pair.snd)
    CertificateScanStatus.none

/-- A small phased program for Phase A.  It assumes the head is already at the
first certificate cell and scans exactly `L` cells.

Phase layout:
* phases `0, ..., L-1`: scan the corresponding certificate offset, update the
  one-hot accumulator, write the scanned bit back unchanged, and move right;
* phase `L`: terminal handoff/decision phase, preserving the accumulator;
* phase `L+1`: idle phase.  The unique accepting state is deliberately not used
  to claim verifier correctness; the useful postcondition is the accumulator in
  phase `L`/`L+1`.
-/
def certificateScanProgram (L : Nat) : ConstStatePhasedProgram (CertificateScanStatus L) where
  numPhases := L + 2
  startPhase := ⟨0, by omega⟩
  startState := CertificateScanStatus.none
  acceptPhase := ⟨L + 1, by omega⟩
  acceptState := CertificateScanStatus.many
  transition := fun i s bit =>
    if hscan : i.val < L then
      (⟨i.val + 1, by omega⟩,
        CertificateScanStatus.register s ⟨i.val, hscan⟩ bit,
        bit,
        Move.right)
    else if hdone : i.val = L then
      (⟨L + 1, by omega⟩, s, bit, Move.stay)
    else
      (i, s, bit, Move.stay)
  timeBound := fun _ => L + 1

@[simp] theorem certificateScanProgram_numPhases (L : Nat) :
    (certificateScanProgram L).numPhases = L + 2 := rfl

@[simp] theorem certificateScanProgram_timeBound (L n : Nat) :
    (certificateScanProgram L).timeBound n = L + 1 := rfl

/-- Local transition lemma for active scan phases: the program advances by one
phase, records the scanned bit in the one-hot accumulator, preserves the tape
symbol, and moves right. -/
theorem certificateScanProgram_transition_scan (L : Nat)
    {i : Fin (certificateScanProgram L).numPhases} (hscan : i.val < L)
    (s : CertificateScanStatus L) (bit : Bool) :
    ((certificateScanProgram L).transition i s bit).fst.val = i.val + 1 ∧
    ((certificateScanProgram L).transition i s bit).snd.fst =
      CertificateScanStatus.register s ⟨i.val, hscan⟩ bit ∧
    ((certificateScanProgram L).transition i s bit).snd.snd.fst = bit ∧
    ((certificateScanProgram L).transition i s bit).snd.snd.snd = Move.right := by
  simp [certificateScanProgram, hscan]

/-- Local transition lemma for the terminal handoff phase after all certificate
cells have been scanned.  The accumulator is preserved and the head stays put. -/
theorem certificateScanProgram_transition_done (L : Nat)
    {i : Fin (certificateScanProgram L).numPhases} (hdone : i.val = L)
    (s : CertificateScanStatus L) (bit : Bool) :
    ((certificateScanProgram L).transition i s bit).fst.val = L + 1 ∧
    ((certificateScanProgram L).transition i s bit).snd.fst = s ∧
    ((certificateScanProgram L).transition i s bit).snd.snd.fst = bit ∧
    ((certificateScanProgram L).transition i s bit).snd.snd.snd = Move.stay := by
  simp [certificateScanProgram, hdone]

/-- The Phase-A scaffold has the declared linear local runtime.  For the
canonical verifier this will be instantiated with
`L = certificateLength n certificateExponent`. -/
theorem certificateScanProgram_runtime (L inputLen : Nat) :
    (certificateScanProgram L).timeBound inputLen = L + 1 := rfl

/-! ## Phase A — read certificate (remaining integration work)

The certificate occupies positions `n .. n + certificateLength n 2 - 1`.
Phase A walks right from the head's initial position 0 through the input
region (`n` cells), enters the certificate region, scans for the unique
`1` bit, and saves the candidate index in state.

**Target signature**:
```
def readCertificate (n : Nat) : PhasedProgram.{0}
theorem readCertificate_run_finds_candidate ...
```
-/

/-! ## Phase B — identify candidate (TODO)

Given the candidate index `k ∈ {0, 1, ..., n+1}`:

  * `k = 0` → candidate is `Circuit.const false`.
  * `k = 1` → candidate is `Circuit.const true`.
  * `k = 2 + i` (for `i ∈ Fin n`) → candidate is `Circuit.input i`.

**Target signature**:
```
def identifyCandidate (n : Nat) : PhasedProgram.{0}
```
-/

/-! ## Phase C — walk table positions (TODO)

Use `BinaryCounter.incrementProgram` to count `j` from 0 to `2^n - 1`.
At each step, drive Phase D to check consistency.

**Target signature**:
```
def walkTablePositions (n : Nat) : PhasedProgram.{0}
```
-/

/-! ## Phase D — check consistency (TODO)

At position `j`:

  * Read `mask_j := tape[j]` (in the first half of the input, positions 0..n-1).
    Actually wait: input length is `2 · 2^n`, so mask is positions 0..2^n-1
    and value is positions 2^n..2·2^n-1.
  * If `mask_j = false`, no constraint at this position; advance.
  * If `mask_j = true`, read `value_j := tape[2^n + j]`.
  * Compute `candidate_eval_at_j` based on the saved candidate:
    - For const `b`: `candidate_eval_at_j = b`.
    - For `input i`: `candidate_eval_at_j = bit i of j` (interpreting `j`
      as an `n`-bit assignment via `vecOfNat`).
  * If `value_j ≠ candidate_eval_at_j`, transition to reject phase.

**Target signature**:
```
def checkConsistencyAt (n : Nat) : PhasedProgram.{0}
```
-/

/-! ## Phase E — final accept (TODO)

If all `j` positions were processed without mismatch, transition to the
accept state.  Otherwise the verifier remains in a non-accept state.

**Target signature**:
```
def finalAccept : PhasedProgram.{0}
```
-/

/-! ## Composed verifier (TODO)

The final verifier composes A → B → (C ∘ D)* → E using
`ConstStatePhasedProgram.seq`.

**Target signature**:
```
noncomputable def canonicalGapMCSPVerifier : Internal.PsubsetPpoly.TM.{0}
```
-/

/-! ## Correctness theorems (TODO)

Once the verifier is composed, the correctness theorems are:

```
theorem canonicalGapMCSPVerifier_runtime_poly ...
theorem canonicalGapMCSPVerifier_correct ...
```

These yield:

```
def canonicalTMWitness :
    Models.GapPartialMCSP_Asymptotic_TMWitness
      Pnp3.Magnification.canonicalAsymptoticSpec where
  M := canonicalGapMCSPVerifier
  c := runtimeExponent
  k := certificateExponent
  runTime_poly := canonicalGapMCSPVerifier_runtime_poly
  correct := canonicalGapMCSPVerifier_correct
```

With `canonicalTMWitness` in hand, every `canonical_*` theorem in
`pnp3/Tests/CanonicalIntegrationTests.lean` becomes unconditional, and the
project advances by closing the entire OPS19/CJW20 asymptotic-side gap.
-/

end GapMCSPVerifier
end PsubsetPpoly
end Internal
end Pnp3
