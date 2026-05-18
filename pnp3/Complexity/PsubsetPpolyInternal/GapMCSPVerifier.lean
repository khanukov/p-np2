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
region (`n` cells), enters the certificate region, scans the first `n + 2`
candidate bits, and saves the one-hot candidate index in finite control.

This is deliberately a **local scaffold**: it gives the first concrete
finite-state navigation/scan phase and its one-step/runtime lemmas, but it
does not claim full verifier correctness and does not construct
`CanonicalAsymptoticVerifierComponents`.  The remaining slack bits of the
`n^2 + 2` certificate are left for later phases/session integration.
-/

/-- Number of size-1 candidates for `n` input variables: constants
`false`/`true` plus the `n` projections. -/
def candidateCount (n : Nat) : Nat := n + 2

@[simp] theorem candidateCount_eq (n : Nat) : candidateCount n = n + 2 := rfl

/-- Phase-A scans exactly the one-hot candidate prefix of the certificate. -/
def phaseACandidateScanSteps (n : Nat) : Nat := candidateCount n

@[simp] theorem phaseACandidateScanSteps_eq (n : Nat) :
    phaseACandidateScanSteps n = n + 2 := rfl

/-- Total Phase-A head moves: cross the `n`-bit input and scan `n + 2`
candidate bits. -/
def phaseATime (n : Nat) : Nat := n + phaseACandidateScanSteps n

@[simp] theorem phaseATime_eq (n : Nat) : phaseATime n = n + (n + 2) := rfl

/-- The part of the certificate consumed by Phase A fits in the canonical
`k = 2` certificate budget. -/
theorem phaseACandidateScanSteps_le_certificateLength (n : Nat) :
    phaseACandidateScanSteps n ≤
      Pnp3.ComplexityInterfaces.certificateLength n certificateExponent := by
  have hn_sq : n ≤ n ^ 2 := by
    cases n with
    | zero => simp
    | succ m =>
        have hone : 1 ≤ Nat.succ m := Nat.succ_pos m
        calc
          Nat.succ m = Nat.succ m * 1 := by rw [Nat.mul_one]
          _ ≤ Nat.succ m * Nat.succ m := Nat.mul_le_mul_left _ hone
          _ = Nat.succ m ^ 2 := by rw [pow_two]
  simp [phaseACandidateScanSteps, candidateCount, certificateExponent,
    Pnp3.ComplexityInterfaces.certificateLength]
  omega

/-- Control state for the Phase-A scan.

The first component is the candidate index found so far, if any.  The second
component is an error flag, set permanently after a second `1` is observed.
Thus `(some k, false)` means that the scanned prefix has been one-hot so far
with unique `1` at candidate `k`; `(none, false)` means all scanned candidate
bits have been `0` so far; and `(_, true)` means the prefix is already invalid.
-/
abbrev CandidateScanState (n : Nat) := Option (Fin (candidateCount n)) × Bool

/-- Initial Phase-A scan state: no candidate found and no error. -/
def candidateScanInit (n : Nat) : CandidateScanState n := (none, false)

/-- Update the finite-control scan summary after reading candidate bit
`offset`.  The scanned tape bit is written back unchanged by the TM program;
all semantic information is carried in this state update. -/
def candidateScanUpdate {n : Nat} (offset : Fin (candidateCount n)) (bit : Bool)
    (st : CandidateScanState n) : CandidateScanState n :=
  if st.2 then
    st
  else if bit then
    match st.1 with
    | none => (some offset, false)
    | some found => (some found, true)
  else
    st

@[simp] theorem candidateScanUpdate_error {n : Nat}
    (offset : Fin (candidateCount n)) (bit : Bool)
    (found : Option (Fin (candidateCount n))) :
    candidateScanUpdate offset bit (found, true) = (found, true) := by
  simp [candidateScanUpdate]

@[simp] theorem candidateScanUpdate_zero {n : Nat}
    (offset : Fin (candidateCount n)) (st : CandidateScanState n)
    (h : st.2 = false) :
    candidateScanUpdate offset false st = st := by
  rcases st with ⟨found, bad⟩
  cases bad <;> simp [candidateScanUpdate] at h ⊢

@[simp] theorem candidateScanUpdate_first_one {n : Nat}
    (offset : Fin (candidateCount n)) :
    candidateScanUpdate offset true (none, false) = (some offset, false) := by
  simp [candidateScanUpdate]

@[simp] theorem candidateScanUpdate_second_one {n : Nat}
    (offset found : Fin (candidateCount n)) :
    candidateScanUpdate offset true (some found, false) = (some found, true) := by
  simp [candidateScanUpdate]

/-- Phase-A program for certificate-region navigation and one-hot candidate
scan.

Phases `0, …, n-1` move right across the original input.  Phases
`n, …, n + candidateCount n - 1` scan the candidate prefix of the certificate,
updating `CandidateScanState n` and moving right.  The final phase is an idle
stop phase whose local state is the scan summary to be consumed by later
verifier phases. -/
def readCertificate (n : Nat) : PhasedProgram.{0} where
  numPhases := phaseATime n + 1
  phaseState := fun _ => CandidateScanState n
  instFin := fun _ => inferInstance
  instDec := fun _ => inferInstance
  startPhase := ⟨0, by omega⟩
  startState := candidateScanInit n
  acceptPhase := ⟨phaseATime n, by omega⟩
  -- This is only a structural stop state for the scaffold.  Full verifier
  -- acceptance is intentionally deferred until the table-consistency phases.
  acceptState := candidateScanInit n
  transition := fun i st bit =>
    if hInput : i.val < n then
      (⟨⟨i.val + 1, by simp [phaseATime, phaseACandidateScanSteps, candidateCount]; omega⟩, st⟩, bit, Move.right)
    else if hScan : i.val < phaseATime n then
      let offset : Fin (candidateCount n) := ⟨i.val - n, by
        simp [phaseATime, phaseACandidateScanSteps, candidateCount] at hScan hInput ⊢
        omega⟩
      (⟨⟨i.val + 1, by simp [phaseATime, phaseACandidateScanSteps, candidateCount] at hScan ⊢; omega⟩, candidateScanUpdate offset bit st⟩, bit, Move.right)
    else
      (⟨⟨phaseATime n, by omega⟩, st⟩, bit, Move.stay)
  timeBound := fun _ => phaseATime n

@[simp] theorem readCertificate_numPhases (n : Nat) :
    (readCertificate n).numPhases = phaseATime n + 1 := rfl

@[simp] theorem readCertificate_timeBound (n inputLen : Nat) :
    (readCertificate n).timeBound inputLen = phaseATime n := rfl

/-- While crossing the original input prefix, Phase A leaves the scan summary
unchanged, writes the scanned bit back, moves right, and advances one phase. -/
theorem readCertificate_transition_input (n : Nat)
    {i : Fin ((readCertificate n).numPhases)} (hInput : i.val < n)
    (st : CandidateScanState n) (bit : Bool) :
    ((readCertificate n).transition i st bit).fst.fst.val = i.val + 1 ∧
    ((readCertificate n).transition i st bit).fst.snd = st ∧
    ((readCertificate n).transition i st bit).snd.fst = bit ∧
    ((readCertificate n).transition i st bit).snd.snd = Move.right := by
  simp [readCertificate, hInput]

/-- In the certificate candidate prefix, Phase A updates exactly by
`candidateScanUpdate` at offset `i - n`, writes the bit back, moves right, and
advances one phase. -/
theorem readCertificate_transition_scan (n : Nat)
    {i : Fin ((readCertificate n).numPhases)}
    (hInputDone : ¬ i.val < n) (hScan : i.val < phaseATime n)
    (st : CandidateScanState n) (bit : Bool) :
    let offset : Fin (candidateCount n) := ⟨i.val - n, by
      simp [phaseATime, phaseACandidateScanSteps, candidateCount] at hScan hInputDone ⊢
      omega⟩
    ((readCertificate n).transition i st bit).fst.fst.val = i.val + 1 ∧
    ((readCertificate n).transition i st bit).fst.snd =
      candidateScanUpdate offset bit st ∧
    ((readCertificate n).transition i st bit).snd.fst = bit ∧
    ((readCertificate n).transition i st bit).snd.snd = Move.right := by
  have hScan' : i.val < n + (n + 2) := by
    simpa [phaseATime, phaseACandidateScanSteps, candidateCount] using hScan
  simp [readCertificate, hInputDone, hScan', phaseATime, phaseACandidateScanSteps, candidateCount]

/-- In the final Phase-A stop phase, the program idles without changing the
scan summary or tape bit. -/
theorem readCertificate_transition_done (n : Nat)
    {i : Fin ((readCertificate n).numPhases)}
    (hDone : phaseATime n ≤ i.val)
    (st : CandidateScanState n) (bit : Bool) :
    ((readCertificate n).transition i st bit).fst.fst.val = phaseATime n ∧
    ((readCertificate n).transition i st bit).fst.snd = st ∧
    ((readCertificate n).transition i st bit).snd.fst = bit ∧
    ((readCertificate n).transition i st bit).snd.snd = Move.stay := by
  have hInput : ¬ i.val < n := by
    have hn_le : n ≤ phaseATime n := by simp [phaseATime]
    omega
  have hScan : ¬ i.val < phaseATime n := by omega
  have hScan' : ¬ i.val < n + (n + 2) := by
    simpa [phaseATime, phaseACandidateScanSteps, candidateCount] using hScan
  simp [readCertificate, hInput, hScan', phaseATime, phaseACandidateScanSteps, candidateCount]

/-- Phase-A has the advertised local runtime: linear in the input-prefix
length plus the `n + 2` candidate bits, and independent of later verifier
phases. -/
theorem readCertificate_runtime (n inputLen : Nat) :
    (readCertificate n).timeBound inputLen = n + (n + 2) := by
  simp [readCertificate, phaseATime, phaseACandidateScanSteps, candidateCount]

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
