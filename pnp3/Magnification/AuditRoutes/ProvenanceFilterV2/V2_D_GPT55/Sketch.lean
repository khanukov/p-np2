import Complexity.Interfaces

/-!
# ProvenanceFilter v2, direction V2-D (rename/provenance signature)

Phase 1 only for `seed_packs/fp3b3_provenance_filter_v2_design/`.

Progress classification: infrastructure / audit-route sketch.  This file only
introduces a candidate `Prop` and a smoke theorem showing that the predicate
elaborates.  It is not a lower-bound theorem, not a promoted guard, and not a
bridge to a final complexity endpoint.
-/

namespace Pnp3
namespace Magnification
namespace AuditRoutes
namespace ProvenanceFilterV2
namespace V2_D_GPT55

open Pnp3.ComplexityInterfaces

namespace FormulaCircuit

/--
Syntactic occurrence count of an ambient input coordinate in a formula.

This is intentionally finer than support cardinality: support only records
whether `i` occurs at least once, while `inputOccurrences i c` records the
multiplicity pattern that survives inside the concrete witness `c`.  Direction
V2-D uses this as a minimal Lean-level stand-in for a provenance signature.
-/
def inputOccurrences {n : Nat} (i : Fin n) : FormulaCircuit n → Nat
  | .const _ => 0
  | .input j => if j = i then 1 else 0
  | .not c => inputOccurrences i c
  | .and c₁ c₂ => inputOccurrences i c₁ + inputOccurrences i c₂
  | .or c₁ c₂ => inputOccurrences i c₁ + inputOccurrences i c₂

end FormulaCircuit

/--
V2-D candidate filter — paper sketch only.

**Excludes NOGO-000001.**  The NOGO-000001 leak packages truth-table/singleton
hardwiring through an overbroad uniform-provenance condition.  This candidate is
not a uniform-provenance umbrella: it demands that every positive length has
full ambient support and that the distinguished ambient coordinate `0` has a
read-once syntactic provenance signature.  Singleton hardwiring, off-slice
constant padding, and other witnesses that exist only because arbitrary slices
can be hardwired do not carry that all-length ambient provenance, so the sketch
intends to reject the `OverbroadUniformProvenance` shape rather than imply it.

**Excludes NOGO-000004/000005.**  The prefix-AND log-width specialisation has
support exactly the first `Nat.log2 (n+1)` (or analogous sublinear) coordinates
at infinitely many large lengths.  The first conjunct below requires support
cardinality to be exactly `n` at every positive length, so the prefix-window
family is rejected.  The second conjunct is deliberately not another cardinality
bound: it records a distinguished-coordinate occurrence signature, forcing Phase
2 to reason about the witness syntax rather than only about the numerical
function `n ↦ |support (w.family n)|`.

**Excludes NOGO-000006.**  The arbitrary-payload obstruction has the shape
`FormulaCircuit.rename σₙ (ttFormula fₙ)`: a truth-table decision tree is
renamed into an ambient alphabet.  Pure rename/support-cardinality filters see
only the final set size and therefore miss the payload.  Here the intended
signature is the occurrence multiplicity of the ambient coordinate `0`.  A
truth-table formula for an all-essential payload uses its source decision
coordinates as branching variables with non-read-once multiplicities, and a
rename merely transports those multiplicities to the image coordinates; it does
not manufacture a canonical read-once ambient anchor.  If `0` is outside the
rename image, full support already fails; if `0` is inside the image, Phase 2
would attack the transported `ttFormula` multiplicity and show it cannot equal
this read-once anchor signature for the NOGO-000006 family.

**Non-vacuity: honest family admitted.**  The intended honest witness is the
standard parity/XOR family on all `n` inputs, encoded as a read-once formula
using the usual Boolean identity `xor a b = (a ∧ ¬ b) ∨ (¬ a ∧ b)` and a
balanced or left-associated fold.  In such an encoding every input coordinate is
in the syntactic support, and coordinate `0` appears exactly once.  Thus parity
should satisfy both conjuncts without relying on a hardwired truth table or on a
length-by-length arbitrary payload choice.

**Self-attack.**  The dangerous weakness is circular provenance: this Phase-1
predicate blesses a syntactic read-once anchor, and an adversary may be able to
wrap a hardwired payload with a harmless-looking read-once parity mask or
re-encode `ttFormula fₙ` into an equivalent formula whose coordinate `0` occurs
once.  Another risk is rejecting harmless renamings of honest families whose
chosen representation puts a non-read-once variable at ambient coordinate `0`;
that would make the filter representation-sensitive rather than language-level.
Phase 2 must therefore prove real exclusion theorems against the formal
NOGO-000001/000004/000005/000006 witnesses and a non-vacuity theorem for a
specified parity representation before this sketch could be promoted.
-/
def ProvenanceFilter_v2_V2_D_GPT55
    {L : Language} (w : InPpolyFormula L) : Prop :=
  (∀ n : Nat, n > 0 → (FormulaCircuit.support (w.family n)).card = n) ∧
  (∀ (n : Nat) (hn : n > 0),
    FormulaCircuit.inputOccurrences ⟨0, hn⟩ (w.family n) = 1)

/-- Phase 1 only — Lean smoke that the predicate elaborates.
    Phase 2 will replace this with real exclusion theorems. -/
theorem v2_D_GPT55_phase1_loaded : True := trivial

end V2_D_GPT55
end ProvenanceFilterV2
end AuditRoutes
end Magnification
end Pnp3
