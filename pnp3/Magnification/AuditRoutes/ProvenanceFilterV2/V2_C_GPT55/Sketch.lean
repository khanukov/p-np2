import Complexity.Interfaces

/-!
# ProvenanceFilter v2 / V2-C / GPT55 — Phase 2 audit start

Progress classification: side-track audit formalization.  This file defines an
operator-reviewable candidate predicate for the `fp3b3` provenance-filter
search and starts Phase 2 with a local zero-extension rejection harness plus a
tiny smoke-test exclusion.  It promotes no guard and introduces no
`SourceTheorem`, `gap_from`, candidate package, or final endpoint.
-/

namespace Pnp3
namespace Magnification
namespace AuditRoutes
namespace ProvenanceFilterV2
namespace V2_C_GPT55

open Pnp3.ComplexityInterfaces

/--
V2-C candidate filter — **bounded incremental information**.

The sketch chooses a concrete, non-support-cardinality notion of consecutive
length provenance.  A witness is accepted when there is one constant `δ` such
that, for every length transition `n → n+1`, (i) the formula size grows by at
most `δ`, and (ii) the `(n+1)`-bit formula is a conservative zero-extension of
the `n`-bit formula: when the new final input is fixed to `false`, evaluation
agrees with the previous length.  Thus every accepted family has a bounded edit
budget plus a semantic compatibility check across adjacent lengths; it cannot
be certified merely from the cardinality of `FormulaCircuit.support`.

1. **Phase-1 intended exclusion target: NOGO-000001.**  `OverbroadUniformProvenance` is too permissive
because it accepts witnesses with no length-to-length compatibility discipline,
including hardwired singleton/truth-table artefacts.  This V2-C sketch demands
one global incremental budget and a semantic zero-extension identity at every
successor length.  A provenance argument that only says "the family is uniformly
available" is therefore insufficient: it must also explain why arbitrary
one-length hardwiring cannot break the successor identity or force an
unbounded-size repair.

2. **Phase-1 intended exclusion target: NOGO-000004/000005.**  The canonical prefix-AND log-width family
changes its Boolean meaning whenever the log-width window grows: setting the new
coordinate to `false` collapses the new prefix conjunction to `false`, while the
previous prefix conjunction may be `true` on the all-true old prefix.  Hence it
violates the zero-extension compatibility clause at each width-increase length,
even before using the bounded-size-increment clause.  This addresses the
scope-corrected prefix-AND obstruction rather than only re-counting its support.

3. **Phase-1 intended exclusion target: NOGO-000006.**  An arbitrary all-essential `ttFormula` payload can
choose a fresh truth table at the next active log-width.  With no relation
between `F n` and `F (n+1)`, the zero-extension identity fails generically.
Even if an adversary forces compatibility on the old half of the table, the
`ttFormula` representation must materialize an arbitrary new half-table on the
new coordinate, causing a size jump far beyond the fixed `δ` budget at infinitely
many width-increase stages.  The attack is therefore aimed at fresh payload
injection, not at support cardinality.

4. **Non-vacuity: honest family admitted.**  The honest family "OR of all input
bits" should be admitted.  It has a fixed recipe: `OR_{n+1}(x,false) = OR_n(x)`,
and a standard right-associated formula grows by a constant number of gates when
one new input is appended.  Thus a small constant `δ` witnesses both the bounded
edit budget and the zero-extension semantic law.  This is a simple AC0 family,
so the predicate is not intended to exclude all natural constructions.

5. **Self-attack.**  The most dangerous attack is payload hiding in places this
Phase-1 predicate does not inspect.  An adversary might encode a large latent
truth table in earlier formula structure, in a decoder that expands a small edit
script, or in an `opCode` whose semantics are not charged by `FormulaCircuit.size`.
A second attack is polarity overfitting: because the sketch chooses the
`false`-padding extension, payloads engineered to be zero-conservative could
still add arbitrary information on the `newBit = true` slice unless the bounded
size-increment clause or a future decoder-normal-form theorem rules them out.
Phase 2 must formalize these attacks before this sketch could be considered a
survivor candidate.
-/
def ProvenanceFilter_v2_V2_C_GPT55
    {L : Language} (w : InPpolyFormula L) : Prop :=
  ∃ δ : Nat,
    (∀ n : Nat,
      FormulaCircuit.size (w.family (n + 1)) ≤
        FormulaCircuit.size (w.family n) + δ) ∧
    (∀ n : Nat, ∀ x : Bitstring n,
      FormulaCircuit.eval (w.family (n + 1))
        (fun i : Fin (n + 1) =>
          if h : i.val < n then x ⟨i.val, h⟩ else false) =
      FormulaCircuit.eval (w.family n) x)

/-!
## Phase 2 audit harness

Progress classification: side-track audit formalization.  The declarations below
start Phase 2 by making the Phase-1 prose checkable: a candidate is rejected as
soon as one adjacent-length zero-extension obligation is falsified.  This is a
local exclusion harness for the V2-C predicate only; it is not a
`PpolyDAG` bridge and is not mainline progress toward `P != NP`.
-/

/--
Phase-2 rejection harness for V2-C.

The second conjunct of `ProvenanceFilter_v2_V2_C_GPT55` is universal in the
length `n` and old input `x`.  Therefore one concrete adjacent-length semantic
mismatch is enough to reject a witness, independently of the bounded-size
increment budget.  Keeping this as a theorem prevents future prose-only
"exclusion" claims from bypassing the actual predicate definition.
-/
theorem v2_C_GPT55_rejects_of_zeroExtension_counterexample
    {L : Language} (w : InPpolyFormula L) (n : Nat) (x : Bitstring n)
    (hbad :
      FormulaCircuit.eval (w.family (n + 1))
        (fun i : Fin (n + 1) =>
          if h : i.val < n then x ⟨i.val, h⟩ else false) ≠
      FormulaCircuit.eval (w.family n) x) :
    ¬ ProvenanceFilter_v2_V2_C_GPT55 w := by
  intro hw
  rcases hw with ⟨_δ, _hsize, hzero⟩
  exact hbad (hzero n x)

/--
A minimal one-step payload used to smoke-test the Phase-2 rejection harness.

At length `0` the formula is the constant `true`; at every positive length it
reads coordinate `0`.  Padding the unique `0`-bit input to length `1` fixes the
new coordinate to `false`, so the length transition `0 → 1` violates V2-C's
zero-extension law.  The example is intentionally tiny: the point is to verify
the rejection mechanism itself, not to claim any lower-bound consequence.
-/
def badOneStepFamily : ∀ n : Nat, FormulaCircuit n
  | 0 => FormulaCircuit.const true
  | n + 1 => FormulaCircuit.input ⟨0, Nat.succ_pos n⟩

/-- Language decided by `badOneStepFamily`, so the witness correctness proof is definitional. -/
def badOneStepLanguage : Language :=
  fun n x => FormulaCircuit.eval (badOneStepFamily n) x

/-- Constant polynomial bound for the one-step smoke-test family. -/
def badOneStepWitness : InPpolyFormula badOneStepLanguage where
  polyBound := fun _ => 1
  polyBound_poly := ⟨1, by intro n; exact Nat.le_add_left 1 _⟩
  family := badOneStepFamily
  family_size_le := by
    intro n
    cases n with
    | zero => simp [badOneStepFamily, FormulaCircuit.size]
    | succ n => simp [badOneStepFamily, FormulaCircuit.size]
  correct := fun _ _ => rfl

/-- The unique empty input, made explicit for the `0 → 1` counterexample. -/
def emptyBits : Bitstring 0 := fun i => Fin.elim0 i

/-- The concrete V2-C zero-extension failure at the first length transition. -/
theorem badOneStep_zeroExtension_counterexample :
    FormulaCircuit.eval (badOneStepWitness.family 1)
      (fun i : Fin 1 =>
        if h : i.val < 0 then emptyBits ⟨i.val, h⟩ else false) ≠
    FormulaCircuit.eval (badOneStepWitness.family 0) emptyBits := by
  simp [badOneStepWitness, badOneStepFamily, FormulaCircuit.eval]

/--
Phase-2 smoke result: V2-C formally rejects the one-step payload.

This is deliberately an audit-side theorem.  It proves that the new rejection
harness has real content and that the V2-C predicate is not merely elaborating;
it does not promote V2-C, create a source theorem, or bridge to `PpolyDAG`.
-/
theorem v2_C_GPT55_rejects_badOneStep :
    ¬ ProvenanceFilter_v2_V2_C_GPT55 badOneStepWitness := by
  exact v2_C_GPT55_rejects_of_zeroExtension_counterexample
    badOneStepWitness 0 emptyBits badOneStep_zeroExtension_counterexample

/-- Phase 2 loaded — the audit harness and concrete smoke exclusion elaborate. -/
theorem v2_C_GPT55_phase2_loaded : True := trivial

end V2_C_GPT55
end ProvenanceFilterV2
end AuditRoutes
end Magnification
end Pnp3
