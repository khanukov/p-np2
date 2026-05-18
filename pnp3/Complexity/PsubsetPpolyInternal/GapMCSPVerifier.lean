import Complexity.PsubsetPpolyInternal.TuringToolkit.Foundation
import Complexity.PsubsetPpolyInternal.TuringToolkit.AtomicPrograms
import Complexity.PsubsetPpolyInternal.TuringToolkit.ConstStatePhasedProgram
import Complexity.PsubsetPpolyInternal.TuringToolkit.BinaryCounter
import Complexity.Interfaces
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

/-! ## Phase A — read certificate

The certificate occupies positions `n .. n + certificateLength n 2 - 1`.
Phase A walks right from the head's initial position 0 through the input
region (`n` cells), enters the certificate region, scans the first `n + 2`
candidate bits, and records whether it has seen no candidate, a unique
candidate index, or a duplicate.  The remaining certificate slack is deliberately
ignored by this phase; later witness-decoder phases may use it for auxiliary
encodings.

This is intentionally only a local TM-verifier phase.  It does **not** claim a
full `accepts_eq`, construct `CanonicalAsymptoticVerifierComponents`, or build
any lower-bound object.
-/

/-- Number of certificate cells available to the canonical verifier. -/
def canonicalCertificateLength (n : Nat) : Nat :=
  ComplexityInterfaces.certificateLength n certificateExponent

@[simp] lemma canonicalCertificateLength_eq (n : Nat) :
    canonicalCertificateLength n = n ^ 2 + 2 := by
  simp [canonicalCertificateLength, certificateExponent, ComplexityInterfaces.certificateLength]

/-- Number of tape cells scanned by Phase A: the whole input plus the whole
certificate.  The candidate scan itself only uses the first `n + 2` certificate
cells, but walking over the slack leaves the head at the end of the certificate
region for the next verifier phase. -/
def readCertificateSteps (n : Nat) : Nat :=
  n + canonicalCertificateLength n

@[simp] lemma readCertificateSteps_eq (n : Nat) :
    readCertificateSteps n = n + (n ^ 2 + 2) := by
  simp [readCertificateSteps]

/-- Phase-A register.  The first component stores the unique candidate index
seen so far (if any); the second component is the duplicate flag.  Once the
duplicate flag is set, downstream phases must reject rather than interpreting
the optional index as valid. -/
abbrev CertificateScanState (n : Nat) := Option (Fin (n + 2)) × Bool

/-- Initial Phase-A register: no candidate bit has been seen and no duplicate
has been detected. -/
def certificateScanInitial (n : Nat) : CertificateScanState n :=
  (none, false)

/-- The register is one-hot-valid exactly when Phase A has seen one candidate
bit and no duplicate candidate bit. -/
def certificateScanValid {n : Nat} (s : CertificateScanState n) : Prop :=
  s.1.isSome ∧ s.2 = false

/-- Read one candidate-region bit at candidate index `idx`.  A `false` bit
leaves the register unchanged; the first `true` bit records `idx`; any later
`true` bit sets the duplicate flag permanently. -/
def certificateScanStep {n : Nat} (s : CertificateScanState n)
    (idx : Fin (n + 2)) (bit : Bool) : CertificateScanState n :=
  if bit then
    if s.2 then
      s
    else
      match s.1 with
      | none => (some idx, false)
      | some old => (some old, true)
  else
    s

@[simp] lemma certificateScanStep_false {n : Nat}
    (s : CertificateScanState n) (idx : Fin (n + 2)) :
    certificateScanStep s idx false = s := by
  simp [certificateScanStep]

@[simp] lemma certificateScanStep_duplicate_true {n : Nat}
    (s : CertificateScanState n) (idx : Fin (n + 2)) (hdup : s.2 = true) :
    certificateScanStep s idx true = s := by
  cases s with
  | mk cand dup =>
      cases dup <;> simp [certificateScanStep] at hdup ⊢

@[simp] lemma certificateScanStep_first_true {n : Nat} (idx : Fin (n + 2)) :
    certificateScanStep (n := n) (none, false) idx true = (some idx, false) := by
  simp [certificateScanStep]

@[simp] lemma certificateScanStep_second_true {n : Nat}
    (old idx : Fin (n + 2)) :
    certificateScanStep (n := n) (some old, false) idx true = (some old, true) := by
  simp [certificateScanStep]

/-- Update the Phase-A register for the cell currently scanned by phase `pos`.
Positions `< n` belong to the input and are ignored.  In the certificate
region, offsets `< n + 2` are one-hot candidate bits and offsets `≥ n + 2` are
certificate slack, ignored by this navigation phase. -/
def certificateScanUpdate (n pos : Nat) (s : CertificateScanState n)
    (bit : Bool) : CertificateScanState n :=
  if _hInput : pos < n then
    s
  else
    let off := pos - n
    if hCand : off < n + 2 then
      certificateScanStep s ⟨off, hCand⟩ bit
    else
      s

@[simp] lemma certificateScanUpdate_input {n pos : Nat}
    (s : CertificateScanState n) (bit : Bool) (hInput : pos < n) :
    certificateScanUpdate n pos s bit = s := by
  simp [certificateScanUpdate, hInput]

@[simp] lemma certificateScanUpdate_slack {n pos : Nat}
    (s : CertificateScanState n) (bit : Bool)
    (hInput : ¬ pos < n) (hSlack : ¬ pos - n < n + 2) :
    certificateScanUpdate n pos s bit = s := by
  simp [certificateScanUpdate, hInput, hSlack]

/-- Phase A as a constant-state phased program.  Phase index `i` means that the
head is positioned at tape cell `i` and the register summarizes all earlier
candidate cells.  Active phases preserve the scanned bit, move right, and update
the register exactly at candidate-region cells.  The final phase idles. -/
def readCertificateProgram (n : Nat) :
    ConstStatePhasedProgram (CertificateScanState n) where
  numPhases := readCertificateSteps n + 1
  startPhase := ⟨0, by omega⟩
  startState := certificateScanInitial n
  acceptPhase := ⟨readCertificateSteps n, by omega⟩
  acceptState := certificateScanInitial n
  transition := fun i s bit =>
    if hActive : i.val < readCertificateSteps n then
      (⟨i.val + 1, by omega⟩,
       certificateScanUpdate n i.val s bit, bit, Move.right)
    else
      (⟨readCertificateSteps n, by omega⟩, s, bit, Move.stay)
  timeBound := fun _ => readCertificateSteps n

/-- Public Phase-A program in the general phased-program interface. -/
def readCertificate (n : Nat) : PhasedProgram.{0} :=
  (readCertificateProgram n).toPhased

@[simp] lemma readCertificateProgram_timeBound (n inputLen : Nat) :
    (readCertificateProgram n).timeBound inputLen = readCertificateSteps n := rfl

@[simp] lemma readCertificate_timeBound (n inputLen : Nat) :
    (readCertificate n).timeBound inputLen = readCertificateSteps n := rfl

/-- Local transition lemma for an active Phase-A cell.  It is the key scaffold
fact needed by later run-level proofs: one active step advances to the next
phase, preserves the tape bit, moves right, and applies the pure scan update to
the finite register. -/
theorem readCertificateProgram_transition_active (n : Nat)
    {i : Fin (readCertificateProgram n).numPhases}
    (hActive : i.val < readCertificateSteps n)
    (s : CertificateScanState n) (bit : Bool) :
    (readCertificateProgram n).transition i s bit =
      (⟨i.val + 1, by
          have hlt : i.val + 1 < readCertificateSteps n + 1 := by omega
          simpa [readCertificateProgram] using hlt⟩,
       certificateScanUpdate n i.val s bit, bit, Move.right) := by
  have hActive' : i.val < n + (n ^ 2 + 2) := by
    simpa [readCertificateSteps] using hActive
  simp [readCertificateProgram, hActive']

/-- Local transition lemma for the terminal Phase-A cell.  Once the scan budget
is exhausted, the phase idles at the terminal phase and does not alter the
register or the scanned bit. -/
theorem readCertificateProgram_transition_done (n : Nat)
    {i : Fin (readCertificateProgram n).numPhases}
    (hDone : ¬ i.val < readCertificateSteps n)
    (s : CertificateScanState n) (bit : Bool) :
    (readCertificateProgram n).transition i s bit =
      (⟨readCertificateSteps n, by omega⟩, s, bit, Move.stay) := by
  have hDone' : ¬ i.val < n + (n ^ 2 + 2) := by
    simpa [readCertificateSteps] using hDone
  have hge : n + (n ^ 2 + 2) ≤ i.val := Nat.le_of_not_gt hDone'
  have hlt : i.val < n + (n ^ 2 + 2) + 1 := by
    simpa [readCertificateProgram] using i.isLt
  have hi : i.val = n + (n ^ 2 + 2) := by omega
  simp [readCertificateProgram, hi]

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
