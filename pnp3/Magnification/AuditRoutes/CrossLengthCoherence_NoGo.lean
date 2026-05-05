/-!
# Cross-Length Coherence — audit target surface (CL-0)

Research Governance v0.1, v0.4.2 Track A-CL0 (Cross-Length
Coherence ideation capture).

This module **records** the named research target surface that
emerged as the unique non-trivial ideation cluster from the
external 12-engineer audit (2026-04 / 2026-05).  All twelve
attempts converged, under several near-synonymous names
(`CrossLengthRecipeCoherence`, `IncrementalRecipe`,
`CoherentDAGFamily`, …), on the intuition that a candidate
provenance Π should constrain not just *individual* lengths but
the *coherence of recipes / information flow across lengths*.

## Status — IMPORTANT, READ TWICE

* This is a **research objective**.
* It is **not** an accepted guard.
* It is **not** a no-go theorem.
* It is **not** a candidate.
* It is **not** evidence of progress.

The CL-0 surface ships only `def : Prop` named *targets* — i.e.
predicate-level objectives that future work can reference.  No
theorem with the signature below has been kernel-checked.  The
cluster's status in `outputs/nogolog.jsonl` is intentionally
empty: NoGoLog is for *formalised* obstructions, and CL-0 has
nothing formalised.

When (and only when) a future engineer kernel-checks one of the
target predicates as a real theorem AND adds the corresponding
`NOGO-NNNNNN` entry, this module's docstring should be updated
to reflect that.  Until then the language stays "target / objective",
not "result / progress".

## What this module does (CL-0 scope)

1. Define toy combinatorial shapes (`ToyFamily`,
   `NaiveCrossLengthCoherence`, `StrongCrossLengthCoherence`,
   `TruthTableHardwired`, `LogWidthHardwired`) at the predicate
   level so research targets can be stated without inventing
   syntax.
2. Provide two `def : Prop` *target* names that the FP-3b.x
   research seed pack and any successor will reference.
3. Smoke witness: `theorem cl0_module_loaded : True := trivial`.
   Pure kernel-trivial; no math content.

## What this module does NOT do (audit-only invariants)

* No `theorem` / `lemma` keyword aside from the smoke witness.
* No proof-suspension placeholders of any kind (the v0.4.2
  hard rule forbids the two well-known ones in any new file).
* No `import` of `Magnification.UnconditionalResearchGap` for
  term-level use.
* No `gap_from_*`, no `ResearchGapWitness`.
* No promotion to `pnp3/Candidates/`.
* No NoGoLog entry.
* No edits to the trust root.

The names below all begin with the
`Pnp3.Magnification.AuditRoutes.CrossLengthCoherence` namespace
prefix and the file lives under `pnp3/Magnification/AuditRoutes/`,
both of which are recognised by the project's quarantine guards
as audit-only zones.
-/

namespace Pnp3
namespace Magnification
namespace AuditRoutes
namespace CrossLengthCoherence

/-!
## Toy shapes.

These are minimal Lean-side stand-ins for the ideation cluster's
intuition.  They are NOT the real predicates a future research
brief would prove against; they are the *named shapes* that let
research targets be stated.
-/

/-- A toy "length-indexed family" of toy items: each length `n`
carries an arbitrary payload value of type `α`.  This is the
minimal carrier on which "across-length" predicates can be
phrased without committing to any particular formula model. -/
structure ToyFamily (α : Type) where
  ofLength : Nat → α

/-- **Naive** cross-length coherence (a placeholder predicate).

This is the *weak* form: only requires that the family's payload
at length `n` is the same constant for every `n`.  It is
deliberately easy to satisfy — including by truth-table
hardwiring shapes — so that the research target
`naive_coherence_accepts_table_hardwiring` (below) can claim
this weakness as the very thing the CL-0 ideation cluster is
trying to escape. -/
def NaiveCrossLengthCoherence {α : Type} (F : ToyFamily α) : Prop :=
  ∀ n m : Nat, F.ofLength n = F.ofLength m

/-- **Strong** cross-length coherence (a placeholder predicate).

The intended *survivor* form: there exists a constructor function
that produces every length's payload from a *fixed*, length-
independent recipe.  This is the shape the ideation cluster
hopes to use to defeat hardwiring across lengths.  In CL-0
this is just a named placeholder — the actual definition will
be supplied by the FP-3b.x research seed pack when it lands. -/
def StrongCrossLengthCoherence {α : Type} (F : ToyFamily α) : Prop :=
  ∃ recipe : Nat → α,
    (∀ n m : Nat, recipe n = recipe m) ∧ (∀ n : Nat, F.ofLength n = recipe n)

/-- **Truth-table hardwiring** marker: every length's payload is
chosen by an oracle, with no constraint relating different
lengths.  This is the trivial way to satisfy
`NaiveCrossLengthCoherence` if `α` is a singleton — and the
shape the ideation cluster hopes `StrongCrossLengthCoherence`
defeats. -/
def TruthTableHardwired {α : Type} (_F : ToyFamily α) : Prop := True

/-- **Log-width hardwiring** marker: at length `n` the family
hardwires a payload determined by a window of `Nat.log2 n + 1`
bits.  At the toy level this is also `True` because the toy
carrier doesn't expose width.  Real research statements at
the FP-3b.x level will replace this with a formula-model
predicate; here we just give the future seed pack a stable
name to reference. -/
def LogWidthHardwired {α : Type} (_F : ToyFamily α) : Prop := True

/-!
## Research targets — Prop-level objectives, NOT theorems.

Each `def : Prop` below names a future research goal.  The
identifiers `CL0_Target_*` are intentionally distinct from any
`theorem` name so a successor module can later state:

    theorem CL0_Target_naive_coherence_accepts_table_hardwiring_proved
        : CL0_Target_naive_coherence_accepts_table_hardwiring := …

without name collision.

These predicates have **no kernel-checked proofs in this
module.**  Until a successor brief kernel-checks them and
appends a corresponding `NOGO-NNNNNN`, treat them as ideation
artefacts only.
-/

/--
Research **objective** for CL-0 weak-coherence NoGo.

NOTE.  This is a research objective, not an accepted guard, not
a no-go theorem, not a candidate, and not evidence of progress.
Until a kernel-checked theorem with this signature is proved
*and* added to `outputs/nogolog.jsonl`, the predicate below is
just a named target.

Expected future theorem shape (proof body NOT yet in scope):

    naive_coherence_accepts_table_hardwiring :
      ∃ (F : ToyFamily Unit),
        TruthTableHardwired F ∧ NaiveCrossLengthCoherence F
-/
def CL0_Target_naive_coherence_accepts_table_hardwiring : Prop :=
  ∃ (F : ToyFamily Unit),
    TruthTableHardwired F ∧ NaiveCrossLengthCoherence F

/--
Research **objective** for CL-0 strong-coherence survivor signal.

NOTE.  Same disclaimer as above: research objective only.

Expected future theorem shape (proof body NOT yet in scope):

    logWidthHardwiring_breaks_strong_coherence :
      ∀ (F : ToyFamily Unit),
        LogWidthHardwired F → ¬ StrongCrossLengthCoherence F
-/
def CL0_Target_logWidthHardwiring_breaks_strong_coherence : Prop :=
  ∀ (F : ToyFamily Unit),
    LogWidthHardwired F → ¬ StrongCrossLengthCoherence F

/-!
## Smoke witness.

Pure kernel-trivial.  Lets `pnp3/Tests/AuditRoutes_CL0_NoGo_Regression.lean`
`#check` an identifier that genuinely loads when the module
elaborates.
-/

theorem cl0_module_loaded : True := trivial

end CrossLengthCoherence
end AuditRoutes
end Magnification
end Pnp3
