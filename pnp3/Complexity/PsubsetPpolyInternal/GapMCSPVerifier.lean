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

/-! ## Phase A — read certificate

The certificate occupies positions `n .. n + certificateLength n 2 - 1`.
Phase A walks right from the head's initial position 0 through the input
region (`n` cells), enters the certificate region, scans for the unique
`1` bit, and saves the candidate index in state.

This session lands the first *local* machine component only.  It deliberately
does **not** state or prove a top-level `accepts_eq`: subsequent phases still
have to interpret the selected candidate and check the partial truth table.
-/

/-- The canonical certificate length used by the verifier scaffold. -/
def certificateRegionLength (n : Nat) : Nat :=
  Pnp3.ComplexityInterfaces.certificateLength n certificateExponent

@[simp] theorem certificateRegionLength_eq (n : Nat) :
    certificateRegionLength n = n ^ 2 + 2 := by
  simp [certificateRegionLength, Pnp3.ComplexityInterfaces.certificateLength,
    certificateExponent]

/-- State carried by Phase A while scanning the certificate region.

The first component records the unique `1` found so far, if any.  The second
component is a sticky duplicate flag: once a second `1` is seen, it remains
`true`.  This is intentionally a finite-control state for each fixed input
length, because `Fin certLen` is finite. -/
abbrev CertificateScanState (certLen : Nat) := Option (Fin certLen) × Bool

/-- Initial Phase-A scan state: no candidate bit has been seen, and no
duplicate has been detected. -/
def CertificateScanState.initial (certLen : Nat) : CertificateScanState certLen :=
  (none, false)

/-- Update the one-hot scan summary at certificate offset `j` after reading
one certificate bit.  A `false` bit leaves the summary unchanged; the first
`true` bit records `j`; every later `true` bit sets the duplicate flag. -/
def updateCertificateScanState {certLen : Nat}
    (st : CertificateScanState certLen) (j : Fin certLen) (bit : Bool) :
    CertificateScanState certLen :=
  if bit then
    match st.1 with
    | none => (some j, st.2)
    | some _ => (st.1, true)
  else
    st

@[simp] theorem updateCertificateScanState_false {certLen : Nat}
    (st : CertificateScanState certLen) (j : Fin certLen) :
    updateCertificateScanState st j false = st := by
  simp [updateCertificateScanState]

@[simp] theorem updateCertificateScanState_true_none {certLen : Nat}
    (j : Fin certLen) (dup : Bool) :
    updateCertificateScanState (none, dup) j true = (some j, dup) := by
  simp [updateCertificateScanState]

@[simp] theorem updateCertificateScanState_true_some {certLen : Nat}
    (old j : Fin certLen) (dup : Bool) :
    updateCertificateScanState (some old, dup) j true = (some old, true) := by
  simp [updateCertificateScanState]

/-- Number of phases in the certificate scanner: `n` input-navigation phases,
`certLen` certificate-scan phases, and one final handoff phase. -/
def readCertificateNumPhases (n : Nat) : Nat :=
  n + certificateRegionLength n + 1

/-- Phase A as a uniform-state phased program.

For phases `< n`, the program only walks right across the original input.
For phases `n ≤ i < n + certLen`, the current tape bit is interpreted as the
certificate bit at offset `i - n` and folded into `CertificateScanState`.  The
last phase is a stable handoff/accept phase for later `seq` composition; its
`acceptState` is not a claim that the full verifier accepts. -/
def readCertificateCS (n : Nat) :
    ConstStatePhasedProgram (CertificateScanState (certificateRegionLength n)) where
  numPhases := readCertificateNumPhases n
  startPhase := ⟨0, by
    simp [readCertificateNumPhases]
  ⟩
  startState := CertificateScanState.initial (certificateRegionLength n)
  acceptPhase := ⟨n + certificateRegionLength n, by
    simp [readCertificateNumPhases]
  ⟩
  acceptState := CertificateScanState.initial (certificateRegionLength n)
  transition := fun i st scan =>
    if hInput : i.val < n then
      (⟨i.val + 1, by
          change i.val + 1 < n + certificateRegionLength n + 1
          omega⟩,
        st, scan, Move.right)
    else if hCert : i.val < n + certificateRegionLength n then
      let j : Fin (certificateRegionLength n) := ⟨i.val - n, by omega⟩
      (⟨i.val + 1, by
          change i.val + 1 < n + certificateRegionLength n + 1
          omega⟩,
        updateCertificateScanState st j scan, scan, Move.right)
    else
      (⟨n + certificateRegionLength n, by
          simp [readCertificateNumPhases]
        ⟩, st, scan, Move.stay)
  timeBound := fun _ => n + certificateRegionLength n

/-- General-phased-program view of the Phase-A certificate scanner. -/
def readCertificate (n : Nat) : PhasedProgram.{0} :=
  (readCertificateCS n).toPhased

@[simp] theorem readCertificateCS_numPhases (n : Nat) :
    (readCertificateCS n).numPhases = n + certificateRegionLength n + 1 := rfl

@[simp] theorem readCertificateCS_timeBound (n inputLen : Nat) :
    (readCertificateCS n).timeBound inputLen = n + certificateRegionLength n := rfl

@[simp] theorem readCertificate_timeBound (n inputLen : Nat) :
    (readCertificate n).timeBound inputLen = n + certificateRegionLength n := rfl

/-- Local transition lemma for the input-navigation part of Phase A.  Before
the certificate starts, the scanner preserves the summary and tape bit, moves
right, and advances one phase. -/
theorem readCertificateCS_transition_input (n : Nat)
    {i : Fin (readCertificateCS n).numPhases} (hi : i.val < n)
    (st : CertificateScanState (certificateRegionLength n)) (scan : Bool) :
    (readCertificateCS n).transition i st scan =
      (⟨i.val + 1, by
          have hit := i.isLt
          simp [readCertificateCS_numPhases] at hit ⊢
          omega⟩, st, scan, Move.right) := by
  simp [readCertificateCS, hi]

/-- Local transition lemma for the certificate-scanning part of Phase A.  At
certificate offset `j`, the scanner folds the scanned bit into the one-hot
summary, preserves the tape bit, moves right, and advances one phase. -/
theorem readCertificateCS_transition_certificate (n : Nat)
    (j : Fin (certificateRegionLength n))
    (st : CertificateScanState (certificateRegionLength n)) (scan : Bool) :
    (readCertificateCS n).transition
        ⟨n + j.val, by
          change n + j.val < n + certificateRegionLength n + 1
          omega⟩ st scan =
      (⟨n + j.val + 1, by
          change n + j.val + 1 < n + certificateRegionLength n + 1
          omega⟩,
        updateCertificateScanState st j scan, scan, Move.right) := by
  have hInput : ¬ n + j.val < n := by omega
  have hjExpanded : j.val < n ^ 2 + 2 := by
    simpa [certificateRegionLength_eq] using j.isLt
  simp [readCertificateCS, hInput, hjExpanded]

/-- Local transition lemma for the final handoff phase.  Once Phase A has
scanned exactly `n + certLen` cells, it stops moving and leaves the accumulated
summary untouched for later phases. -/
theorem readCertificateCS_transition_done (n : Nat)
    (st : CertificateScanState (certificateRegionLength n)) (scan : Bool) :
    (readCertificateCS n).transition
        ⟨n + certificateRegionLength n, by
          simp [readCertificateCS_numPhases]
        ⟩ st scan =
      (⟨n + certificateRegionLength n, by
          simp [readCertificateCS_numPhases]
        ⟩, st, scan, Move.stay) := by
  simp [readCertificateCS]

/-- Runtime accounting for Phase A: the declared runtime is exactly the number
of cells traversed before the handoff phase, namely the input prefix plus the
certificate region. -/
theorem readCertificateCS_runtime_exact (n inputLen : Nat) :
    (readCertificateCS n).timeBound inputLen = n + certificateRegionLength n := rfl

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
