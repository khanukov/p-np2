import Pnp4.Frontier.OneTapeMagnification.Counting
import Pnp4.Frontier.OneTapeMagnification.DeterministicComplement

/-!
# Deterministic local-HSG exclusion for coMCSP

The randomized CHMY route is usually stated with a PRG and an acceptance-gap
calculation.  For the deterministic magnification endpoint, less is needed.
If the bounded-time acceptance predicate of a deterministic one-tape machine
is exactly the hard truth tables, then its accepting set has density above one
half by elementary DAG-code counting.  A hitting set for that fixed machine
must therefore produce an accepted table.  But circuit-locality says that
every fixed-seed output has a small DAG, so none of those outputs is hard.

This file proves that finite contradiction directly.  It makes no averaging
assumption, assigns no probability distribution to seeds, and therefore also
identifies the exact way in which the support of a signed weighted PRG could
be sufficient: only the existence of a hitting seed is consumed.

The theorem is conditional on a concrete generator satisfying a concrete
dense-hitting statement for the concrete machine.  Existence of the missing
small local HSG is not postulated, packaged, or hidden here.
-/

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

open StreamingMagnification
open StreamingMagnification.TotalSearch
open Counting

/-- A finite predicate has density strictly above one half if it contains an
explicit witness set with more than half of all truth tables.  Using a subset
witness avoids any decidability assumption on the predicate itself. -/
def DenseAboveHalf (n : Nat) (predicate : TruthTable n → Prop) : Prop :=
  ∃ witnesses : Finset (TruthTable n),
    2 ^ (2 ^ n) < witnesses.card * 2 ∧
    ∀ table, table ∈ witnesses → predicate table

/-- Tables outside the canonical-code image form an explicit subset of the
genuinely hard truth tables. -/
def hardWitnessTables (n threshold : Nat) : Finset (TruthTable n) :=
  Finset.univ \ easyTablesByCode n threshold

theorem mem_hardWitnessTables_not_hasCircuit
    {n threshold : Nat} {table : TruthTable n}
    (hMem : table ∈ hardWitnessTables n threshold) :
    ¬ HasCircuit n threshold table := by
  apply not_hasCircuit_of_not_mem_easyTablesByCode
  simpa [hardWitnessTables] using hMem

/-- The code-length gap makes the explicit hard witness set larger than half
of the truth-table cube.  The stronger counting lemma actually gives a
three-quarter bound; only the half-density needed by the HSG endpoint is kept
in the conclusion. -/
theorem card_hardWitnessTables_gt_half
    (n threshold : Nat)
    (hLength : DAGCodec.codeLength n threshold + 2 < 2 ^ n) :
    2 ^ (2 ^ n) < (hardWitnessTables n threshold).card * 2 := by
  have hEasy := four_mul_card_easyTablesByCode_lt n threshold hLength
  have hCard :
      (hardWitnessTables n threshold).card =
        2 ^ (2 ^ n) - (easyTablesByCode n threshold).card := by
    rw [hardWitnessTables, Finset.card_sdiff (Finset.subset_univ _)]
    simp
  rw [hCard]
  omega

/-- Standard-DAG coMCSP is dense above one half under the explicit finite
code-length inequality. -/
theorem coMCSP_denseAboveHalf
    (n threshold : Nat)
    (hLength : DAGCodec.codeLength n threshold + 2 < 2 ^ n) :
    DenseAboveHalf n (fun table => ¬ HasCircuit n threshold table) := by
  refine ⟨hardWitnessTables n threshold,
    card_hardWitnessTables_gt_half n threshold hLength, ?_⟩
  intro table hMem
  exact mem_hardWitnessTables_not_hasCircuit hMem

/-- Acceptance of one truth table by the concrete deterministic machine
within the stated step budget. -/
def deterministicTableAcceptance
    (machine : DeterministicMachine) {n : Nat}
    (steps : Nat) (table : TruthTable n) : Prop :=
  AcceptsWithin machine (tableBits table) steps

/-- Exact bounded-time acceptance behavior for the complement of standard-DAG
MCSP at one finite length and threshold.  This equivalence alone does not
assert that the machine halts on easy inputs; a total decider is a special
case. -/
def ExactCoMCSPBehavior
    (machine : DeterministicMachine)
    (n threshold steps : Nat) : Prop :=
  ∀ table : TruthTable n,
    deterministicTableAcceptance machine steps table ↔
      ¬ HasCircuit n threshold table

/-- The support-only property needed from a deterministic HSG for this fixed
machine: if this machine's bounded-time accepting set has density above one
half, some fixed-seed output is accepted. -/
def HitsDenseOneTapeAcceptance
    (machine : DeterministicMachine)
    {n threshold : Nat}
    (generator : DAGLocalGenerator n threshold)
    (steps : Nat) : Prop :=
  DenseAboveHalf n (deterministicTableAcceptance machine steps) →
    ∃ seed : FiniteBitTape generator.seedBits,
      deterministicTableAcceptance machine steps (generator.generate seed)

/-- A local generator cannot itself hit the hard-table predicate at the same
threshold: each of its fixed-seed outputs is certified easy. -/
theorem localGenerator_does_not_hit_coMCSP
    {n threshold : Nat}
    (generator : DAGLocalGenerator n threshold) :
    ¬ (∃ seed : FiniteBitTape generator.seedBits,
        ¬ HasCircuit n threshold (generator.generate seed)) := by
  rintro ⟨seed, hHard⟩
  exact hHard (generator.image_easy seed)

/-- Deterministic local-HSG capstone at one finite length.  Dense hitting for
the fixed machine plus fixed-seed DAG locality excludes exact bounded-time
coMCSP acceptance behavior, and hence excludes a total coMCSP decider. -/
theorem localGenerator_denseHitting_excludes_exactCoMCSP
    (machine : DeterministicMachine)
    {n threshold : Nat}
    (generator : DAGLocalGenerator n threshold)
    (steps : Nat)
    (hLength : DAGCodec.codeLength n threshold + 2 < 2 ^ n)
    (hHits : HitsDenseOneTapeAcceptance machine generator steps) :
    ¬ ExactCoMCSPBehavior machine n threshold steps := by
  intro hBehavior
  have hDense :
      DenseAboveHalf n (deterministicTableAcceptance machine steps) := by
    rcases coMCSP_denseAboveHalf n threshold hLength with
      ⟨witnesses, hCard, hHard⟩
    refine ⟨witnesses, hCard, ?_⟩
    intro table hMem
    exact (hBehavior table).2 (hHard table hMem)
  rcases hHits hDense with ⟨seed, hAccept⟩
  have hHard : ¬ HasCircuit n threshold (generator.generate seed) :=
    (hBehavior (generator.generate seed)).1 hAccept
  exact hHard (generator.image_easy seed)

/-- Exact two-outcome deterministic MCSP decision behavior.  Every easy table
is accepted within the budget and every hard table is rejected within it, with
both converses explicit. -/
def ExactMCSPDecisionBehavior
    (machine : DeterministicMachine)
    (n threshold steps : Nat) : Prop :=
  ∀ table : TruthTable n,
    (AcceptsWithin machine (tableBits table) steps ↔
      HasCircuit n threshold table) ∧
    (RejectsWithin machine (tableBits table) steps ↔
      ¬ HasCircuit n threshold table)

/-- Complementing an exact MCSP decider produces the exact bounded-time coMCSP
acceptance predicate consumed by the deterministic HSG capstone. -/
theorem complementMachine_exactCoMCSPBehavior_of_exactMCSPDecision
    (machine : DeterministicMachine)
    (n threshold steps : Nat)
    (hBehavior : ExactMCSPDecisionBehavior machine n threshold steps) :
    ExactCoMCSPBehavior (complementMachine machine) n threshold steps := by
  intro table
  unfold deterministicTableAcceptance
  rw [complementMachine_acceptsWithin_iff_rejectsWithin]
  exact (hBehavior table).2

/-- Direct MCSP-decider form: it is enough that the local generator densely
hits the accepting set of the complemented machine. -/
theorem localGenerator_denseHitting_excludes_exactMCSPDecision
    (machine : DeterministicMachine)
    {n threshold : Nat}
    (generator : DAGLocalGenerator n threshold)
    (steps : Nat)
    (hLength : DAGCodec.codeLength n threshold + 2 < 2 ^ n)
    (hHits :
      HitsDenseOneTapeAcceptance (complementMachine machine) generator steps) :
    ¬ ExactMCSPDecisionBehavior machine n threshold steps := by
  intro hBehavior
  exact localGenerator_denseHitting_excludes_exactCoMCSP
    (complementMachine machine) generator steps hLength hHits
    (complementMachine_exactCoMCSPBehavior_of_exactMCSPDecision
      machine n threshold steps hBehavior)

end OneTapeMagnification
end Frontier
end Pnp4
