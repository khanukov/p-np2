import Magnification.UnconditionalResearchGap
import Tests.FormulaSupportBoundsFalsifiabilityProbe

/-!
# FixedParams Probe — audit-only surface (FP-1)

Research Governance v0.1, FP-1 (FixedParams Probe preparation).

This module is the **audit-facing surface** for the FixedParams
Probe.  It is preparatory: it does NOT attempt Outcome A
(formal `→ False` for the route), Outcome B (factorisation through
known guards), or Outcome C (promotion of a new candidate
`SourceTheorem`).  Those are FP-2 / FP-3 / FP-4.

What this module does:

1. Re-export the key existing identifiers under canonical
   `FixedParamsProbe.*` audit names.
2. Surface the hardwiring obstruction (Probe 2 of the
   falsifiability probe) as the formal artifact backing the
   `HardwiringGuard` entry of `spec/known_guards.toml`.
3. Provide nothing else: no new theorems, no new predicates, no
   `class`/`instance`/`Fact` payload.

What this module does NOT do (per FP-1 scope):

* No new `Prop` defining a candidate provenance Π.
* No `gap_from_*` bridge.
* No `SourceTheorem_*`.
* No reference to `ResearchGapWitness`.
* No edits to the trust root
  (`Pnp3.Complexity.Interfaces`, `Pnp3.Magnification.UnconditionalResearchGap`,
  `Pnp3.Magnification.FormulaSupportBoundsPartial_fromPipeline_fixedParams`).
* No `class`/`instance`/`Fact`/`opaque`/`default_instance`.

The names below all begin with the `FixedParamsProbe.` namespace
prefix and the file lives under `pnp3/Magnification/AuditRoutes/`,
both of which are recognised by the project's quarantine guards as
audit-only zones.
-/

namespace Pnp3
namespace Magnification
namespace AuditRoutes
namespace FixedParamsProbe

open Pnp3.Magnification (
  FormulaSupportBoundsPartial_fromPipeline_fixedParams
  OverbroadUniformFormulaProvenance
)

/-!
## Audit-only aliases for the FixedParams route shape.

Each `abbrev` below re-exports an existing identifier under a
canonical name that the FP-2/FP-3/FP-4 probes will reference.
-/

/-- Audit alias for `FormulaSupportBoundsPartial_fromPipeline_fixedParams`,
the predicate that the FixedParams Probe wants to either kill
(Outcome A) or factor through known guards (Outcome B). -/
abbrev FixedParamsRoute
    (ac0 : ThirdPartyFacts.AC0Parameters) (sb : Nat → Nat) : Prop :=
  FormulaSupportBoundsPartial_fromPipeline_fixedParams ac0 sb

/-- Audit alias for `OverbroadUniformFormulaProvenance`, the broad
provenance shape that, paired with `FixedParamsRoute`, reconstructs
the refuted `FormulaSupportRestrictionBoundsPartial`.  Used as the
"counterexample provenance" baseline in FP-2. -/
abbrev OverbroadUniformProvenance
    (ac0 : ThirdPartyFacts.AC0Parameters) : Prop :=
  OverbroadUniformFormulaProvenance ac0

/-!
## Hardwiring obstruction surface.

Probe 2 of `pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean`
constructs a `PpolyFormula` witness for `gapPartialMCSP_Language` by
truth-table hardwiring.  Any candidate provenance Π that fails to
exclude such a witness is automatically vacuous: the singleton
truth-table family satisfies "arbitrary `PpolyFormula` quantification"
without doing any real work.

`HardwiringObstruction` re-exposes the formal artifact
(`Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe.fixedSlice_gapPartialMCSP_in_PpolyFormula`)
under a stable name so that
`spec/known_guards.toml::guards.HardwiringGuard` can refer to it
without fragility.
-/

/-- Audit alias for the truth-table hardwiring lemma (Probe 2). -/
def HardwiringObstruction
    (p : Pnp3.Models.GapPartialMCSPParams) :
    Pnp3.ComplexityInterfaces.PpolyFormula
        (Pnp3.Models.gapPartialMCSP_Language p) :=
  Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe.fixedSlice_gapPartialMCSP_in_PpolyFormula p

/-- The hardwiring guard, in audit-only form: every Partial-MCSP
slice has at least one `PpolyFormula` witness, and that witness is
exhibited by the truth-table construction above.  This is the formal
backing of `spec/known_guards.toml::guards.HardwiringGuard`.

A candidate provenance Π that does not formally exclude this witness
shape (or factor through it) is deemed vacuous in FP-2. -/
def HardwiringGuard : Prop :=
  ∀ (p : Pnp3.Models.GapPartialMCSPParams),
    Nonempty (Pnp3.ComplexityInterfaces.PpolyFormula
                (Pnp3.Models.gapPartialMCSP_Language p))

/-- The hardwiring guard is inhabited via Probe 2. -/
theorem hardwiring_guard_holds : HardwiringGuard :=
  fun p => ⟨HardwiringObstruction p⟩

/-!
## Outcome A — overbroad uniform provenance baseline (FP-2).

The smallest-possible-scope FP-2 result: the route fails for the
**single** candidate provenance `Π = OverbroadUniformProvenance ac0`.

This is **not** a claim that the FixedParams route is dead in
general.  It is a re-export, under an audit-only name, of the
already-formalised Probe 8a leak theorem
(`false_of_fixedParams_and_uniformProvenance` in
`pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean`):
combining `FixedParamsRoute ac0 sb` with the overbroad provenance
shape reconstructs the refuted `FormulaSupportRestrictionBoundsPartial`
predicate, and Probe 3 of the falsifiability audit refutes that.

The wrapper exists so that:

1. Future FP-3 / FP-4 work has a stable audit name to reference
   (they may NOT inline the underlying Probe 8a theorem; this
   wrapper is the canonical access point).
2. The verifier-side NoGo log entry has a stable
   `formal_witness` pointer (file:line of this theorem).
3. Any future `Π` that is at least as strong as the overbroad
   shape is automatically dead by composition with this theorem.

This theorem proves **`False`**, not `→ ResearchGapWitness`.  It is
not a bridge; it is an obstruction.  An honest Outcome A for an
arbitrary candidate `Π` would require additionally showing that
`Π → OverbroadUniformProvenance ac0`, which is in general open.
-/

/-- **Outcome A baseline** (FP-2): pairing `FixedParamsRoute ac0 sb`
with the overbroad uniform provenance shape is ex-falso.

Proof: re-export of
`Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe.false_of_fixedParams_and_uniformProvenance`
under the canonical audit name.  No new mathematics.

Naming convention: `NoGo_*` prefix marks a theorem whose conclusion
is `False` (not `ResearchGapWitness`).  These are obstructions used
by FP-N analysis, not bridges to the final target. -/
theorem NoGo_FixedParamsRoute_with_OverbroadUniformProvenance
    (p : Pnp3.Models.GapPartialMCSPParams)
    (ac0 : Pnp3.ThirdPartyFacts.AC0Parameters)
    (sb : Nat → Nat)
    (hUniform : OverbroadUniformProvenance ac0)
    (hRoute   : FixedParamsRoute ac0 sb) :
    False :=
  Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe.false_of_fixedParams_and_uniformProvenance
    p ac0 sb hUniform hRoute

/-!
## FP-3 anchor — `ProvenanceFilter_v1` (informal placeholder, NO Lean
artifact).

`spec/known_guards.toml::guards.ProvenanceFilter_v1` reserves a stable
name for the planned filter that, if formalized, would prune truth-
table-like AC0 family witnesses to non-singleton, non-hardwired AC0
families.  It is the *intended* Outcome-B partner of
`HardwiringGuard`: the conjunction `HardwiringGuard ∧ ProvenanceFilter_v1`
is meant to become non-trivial once the second conjunct is no longer a
Lean theorem.

The registry's `ProvenanceFilter_v1` entry stays `status = "informal"`
and `formal_name = ""`.  The audit-only experimental shapes below
(`FP3Attempt.*`) are NOT promoted to the registry and are NOT
admissible for any Outcome-B reduction.  They exist solely to record
the FP-3 actual self-attack work.
-/

/-!
## FP-3 actual — experimental candidate `SupportFunctionalDiversity`
(audit-only, NOT promoted to `spec/known_guards.toml`).

This namespace encodes ONE concrete Lean shape proposed during FP-3
actual self-attack and the formal artifact that defeats the truth-
table hardwiring attack against it (Test 3 of the four-test self-
attack protocol).

The candidate is intentionally NOT promoted to the known-guards
registry.  Its purpose is to record the FP-3 actual report's
mathematical content under verifier control: future drift to the
candidate's behaviour breaks the regression test in
`pnp3/Tests/FixedParams_Probe_NoGo.lean`, which is what we want.

See `FixedParams_Probe.md` for the full self-attack report,
including the multi-slice hardwiring caveat and the explicit reason
the candidate is NOT promoted to FP-4.
-/

namespace FP3Attempt

open Pnp3.ComplexityInterfaces

/-- **Candidate `ProvenanceFilter_v1` shape** (audit-only).

The support-cardinality function `n ↦ |support (w.family n)|` of the
record `w : InPpolyFormula L` is required to be:

1. **Unbounded**: for every `B`, some length witnesses support card > B.
2. **Infinitely often non-saturated**: for every threshold `N`, some
   length `n ≥ N` witnesses `support card < n`.  This is strictly
   weaker than "eventually sublinear" — the support function is
   allowed to hit `n` (full saturation) at infinitely many lengths,
   as long as it also drops strictly below `n` at infinitely many
   other lengths.

Together, (1) and (2) forbid two degenerate shapes simultaneously:

* shapes with bounded support (incl. the truth-table hardwired witness
  of Probe 2, whose support is `n₀` at one length and `0` elsewhere);
* shapes with always-saturated support (e.g. `support n = n` at every
  length, which is full-truth-table at every length).

Defined at the `InPpolyFormula` record level rather than the `Prop`
existential, because `Classical.choose` of `PpolyFormula L = ∃ _, True`
is opaque and gives no handle on the underlying `family`. -/
def InSupportFunctionalDiversity {L : Pnp3.ComplexityInterfaces.Language}
    (w : InPpolyFormula L) : Prop :=
  (∀ B : Nat, ∃ n, B < (FormulaCircuit.support (w.family n)).card) ∧
  (∀ N : Nat, ∃ n, N ≤ n ∧ (FormulaCircuit.support (w.family n)).card < n)

/-- **Test 3 (hardwiring attack defeat)** at the record level.

Any `InPpolyFormula` record whose `polyBound` is uniformly bounded by
some constant `B` automatically fails `InSupportFunctionalDiversity`,
because

```
support card  ≤  formula size  ≤  polyBound n  ≤  B
```

and so the unboundedness conjunct of the diversity condition is
violated.

The Probe-2 truth-table hardwired witness
(`Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe.fixedSlice_gapPartialMCSP_in_PpolyFormula`)
is an instance of this lemma: it builds an `InPpolyFormula` record
with `polyBound m = if m = n₀ then c₀_size else 1`, hence bounded by
`max(c₀_size, 1)`.  Therefore that record violates the candidate
filter.

This is a clean Outcome-A-style obstruction against the SPECIFIC
hardwiring shape used by the active leak proof — but NOT against
log-width hardwiring (truth-table at width `k(n) = O(log n)`
selected variables), which is polynomially-bounded and therefore
admissible inside `InPpolyFormula L`.  See `FixedParams_Probe.md`
§FP-3 actual / §8.7 for the caveat (FP-3b.0 update: the original
"alternating-slice full-width TT" caveat was incorrect — that
shape violates `polyBound_poly` and cannot be a counterexample;
the real residual concern is log-width TT). -/
theorem InSupportFunctionalDiversity_excludes_uniformPolyBound
    {L : Pnp3.ComplexityInterfaces.Language}
    (w : InPpolyFormula L) (B : Nat)
    (hBound : ∀ n, w.polyBound n ≤ B) :
    ¬ InSupportFunctionalDiversity w := by
  intro hDiv
  obtain ⟨hUnbounded, _⟩ := hDiv
  obtain ⟨n, hn⟩ := hUnbounded B
  have h1 : (FormulaCircuit.support (w.family n)).card
              ≤ FormulaCircuit.size (w.family n) :=
    FormulaCircuit.support_card_le_size (w.family n)
  have h2 : FormulaCircuit.size (w.family n) ≤ w.polyBound n :=
    w.family_size_le n
  have h3 : w.polyBound n ≤ B := hBound n
  have hLe : (FormulaCircuit.support (w.family n)).card ≤ B :=
    Nat.le_trans h1 (Nat.le_trans h2 h3)
  exact (Nat.not_lt_of_ge hLe) hn

end FP3Attempt

/-!
## FP-3b.1 — audit-only Lean skeleton (`FP3b1` namespace).

Research Governance v0.1, Autoresearch MVP / FP-3b.1.

This namespace ships the **structural scaffolding** for the
log-width / power-of-two-slice hardwiring adversary described in
`seed_packs/fp3b1_log_width_hardwiring/README.md`.  It is
intentionally minimal:

* `adversaryFamily n` is `FormulaCircuit.const false` at every
  length — a trivial placeholder family;
* `adversaryLanguage` is **defined as** `eval (adversaryFamily n) x`,
  per the FP-3b.0 packaging correction (NOT `fun _ _ => false`,
  which would force the body of `adversaryFamily` to evaluate to
  `false` everywhere);
* `adversaryWitness : InPpolyFormula adversaryLanguage` is a
  complete `InPpolyFormula` record over the trivial family,
  demonstrating that the corrected packaging compiles end-to-end
  and that `correct := by intro n x; rfl` is sound.

The skeleton **does NOT** satisfy
`FP3Attempt.InSupportFunctionalDiversity` — `const false` has
empty support at every length, so the unboundedness conjunct
fails by inspection.  This is intentional: FP-3b.1 ships the
scaffolding; FP-3b.2 fills in a real log-width truth-table-shaped
family that DOES satisfy the diversity property.  Because no
incomplete-proof markers is allowed in the active tree, the diversity-witness
theorem is preserved here as a docstring goal rather than a
half-proved `theorem`.

What FP-3b.1 establishes (audit-only):

1. The packaging correction from FP-3b.0 is sound: defining
   `adversaryLanguage n x := eval (adversaryFamily n) x` makes the
   `correct` field of `InPpolyFormula` trivially `rfl`, regardless
   of the family's body.
2. A full `InPpolyFormula` record can be assembled in the
   `FP3Attempt.FP3b1` namespace without touching the trust root,
   without introducing typeclass / axiom / opaque payload, and
   without modifying existing FP-3 / FP-3-actual artifacts.
3. FP-3b.2 (the actual log-width adversary) can be a drop-in
   replacement of `adversaryFamily`'s body, with the surrounding
   record and language definitions unchanged.

What FP-3b.1 does NOT establish:

* No diversity-satisfaction proof.
* No NOGO-000003 upgrade to `status = "formalized"` (it stays
  `needs_review`).
* No `ProvenanceFilter_v1` promotion (stays informal).
* No `Candidates/<id>/` directory (audit-only routing).
* No bridge / SourceTheorem / final endpoint.
-/

namespace FP3b1

open Pnp3.ComplexityInterfaces

/-- **FP-3b.1 placeholder adversary family.**

This is INTENTIONALLY trivial (`FormulaCircuit.const false` at
every length) so that the surrounding `InPpolyFormula` packaging
compiles.  The corrected-packaging trick — defining the language
as `eval (family n)` rather than `fun _ _ => false` — works for
ANY `family : ∀ n, FormulaCircuit n`, including the trivial body
here.

FP-3b.2 will replace this body with a log-width / power-of-two-
slice truth-table-shaped construction (see
`seed_packs/fp3b1_log_width_hardwiring/README.md` §5–6 for the
construction and §6 for the lemma TODOs).  The surrounding
`adversaryLanguage` and `adversaryWitness` definitions do NOT
need to change. -/
def adversaryFamily : ∀ n : Nat, FormulaCircuit n :=
  fun _ => FormulaCircuit.const false

/-- **FP-3b.0 packaging correction (verified here).**

The language is defined as the family's evaluation, NOT as a
fixed function like `fun _ _ => false`.  This makes the
`correct` field of `InPpolyFormula adversaryLanguage` trivially
provable by `rfl`, regardless of `adversaryFamily`'s body.

The original FP-3b.0 sketch in `outputs/nogolog.jsonl::NOGO-000003`
notes mentioned packaging into `InPpolyFormula (fun _ _ => false)`.
That packaging is INCORRECT for an arbitrary truth-table
hardwired family because `correct` would not hold for `L = const
false` unless the family also evaluates to `false` everywhere —
which is NOT the case for an adversary that hardwires arbitrary
Boolean functions on a log-width window. -/
def adversaryLanguage : Pnp3.ComplexityInterfaces.Language :=
  fun n x => FormulaCircuit.eval (adversaryFamily n) x

/-- **FP-3b.1 placeholder InPpolyFormula record.**

Polynomial bound is the trivial `polyBound n := 1`; for the real
FP-3b.2 log-width adversary this will become
`polyBound n := 6 * (n + 1)` (or similar, derived from
`(ttFormula at width logWidth n).size ≤ 6 * 2^(logWidth n) ≤
6 * (n + 1)`).  All four field-proofs degenerate to `rfl` /
`decide` here because the family is constant. -/
def adversaryWitness : InPpolyFormula adversaryLanguage where
  polyBound := fun _ => 1
  polyBound_poly := ⟨1, by intro n; exact Nat.le_add_left 1 _⟩
  family := adversaryFamily
  family_size_le := fun _ => by
    show FormulaCircuit.size (FormulaCircuit.const false) ≤ 1
    exact Nat.le.refl
  correct := fun _ _ => rfl

/-- **FP-3b.2 GOAL (not proved here).**

The diversity-witness theorem that FP-3b.2 must close:

```lean
theorem adversary_satisfies_diversity :
    FP3Attempt.InSupportFunctionalDiversity adversaryWitness
```

The FP-3b.1 skeleton's `adversaryFamily := fun _ => const false`
does NOT satisfy this — `const false` has empty support at every
length and the unboundedness conjunct
`∀ B, ∃ n, B < (support (family n)).card` fails for any `B ≥ 0`
because the support cardinality is identically `0`.

To close the goal, FP-3b.2 must:

1. replace `adversaryFamily`'s body with a log-width TT
   construction (or the simpler power-of-two-slice variant);
2. update `polyBound` (e.g. to `6 * (n + 1)`) and re-prove
   `polyBound_poly` and `family_size_le`;
3. derive `(family n).support.card` is unbounded as `n → ∞`;
4. derive `(family n).support.card < n` infinitely often;
5. compose the two diversity conjuncts into the final theorem.

The supporting lemmas (`Nat.log` helpers, `(ttFormula f).size ≤
6 * 2^k`, `FormulaCircuit.rename` size + support transport) are
enumerated in `seed_packs/fp3b1_log_width_hardwiring/README.md`
§6.  None of them exist as stand-alone Lean lemmas yet; FP-3b.2
will add them either as fresh top-level lemmas in this audit
module or as a small new audit module under
`pnp3/Magnification/AuditRoutes/`. -/
example : True := trivial   -- placeholder so the docstring above
                            -- attaches to a real declaration

end FP3b1

end FixedParamsProbe
end AuditRoutes
end Magnification
end Pnp3
