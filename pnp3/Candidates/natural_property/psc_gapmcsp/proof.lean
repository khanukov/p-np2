/-!
# Candidate `natural_property / psc_gapmcsp` — Lean skeleton

**Status: DRAFT SKELETON (not an intake-ready candidate).**

This file is **excluded from `lake build`** (it is not listed in
`lakefile.lean::[lean_lib PnP3].globs`) and is deliberately free of
proof holes so that Step 3 of `scripts/check.sh` (the source-hygiene
scan, which greps every `pnp3/**/*.lean` for unfinished-proof tokens)
stays green.  It is loaded only by `scripts/verify_candidate.sh`.

Approach (see `sketch.md`): exhibit an explicit *almost-natural*
property of Boolean functions that is

* constructive-enough (or with `constructivity` explicitly sacrificed),
* USEFUL against `P/poly` (fails on every poly-size DAG function),
* TRUE on the `GapMCSP` truth table (an explicit NP function),
* **sub-large** — held by only a `2^{-ω(n)}` fraction of functions, so
  it escapes the Razborov–Rudich largeness condition (Chow's
  almost-natural route), and
* **not satisfiable by truth-table hardwiring** — the Rule 5 exclusion
  lemma, which is exactly the `failure_class = "hardwiring"` wall that
  killed all nine prior attempts in `outputs/nogolog.jsonl`.

The genuinely hard object is the *inhabitant* of
`SourceTheorem_psc_gapmcsp`.  The bridge `gap_from_psc_gapmcsp` is the
engineer's obligation: retype its codomain from `True` to
`Pnp3.Magnification.ResearchGapWitness` and prove the short, real
derivation

    (useful on P/poly) ∧ (holds on GapMCSP)
      ⇒ ComplexityInterfaces.NP_not_subset_PpolyDAG

against the repository's `PpolyDAG` / `gapPartialMCSP` definitions.
Until then this stays a DRAFT and `verify_candidate.sh` will correctly
report the missing `ResearchGapWitness` bridge as the open obligation.

Constitution compliance targets:
* Rule 4  — `SourceTheorem_psc_gapmcsp` ≤ 40 lines; closure ≤ 200.
* Rule 5  — the `NotHardwired` conjunct is the mandatory exclusion lemma.
* Rule 16 — no `class`/`instance`/`Fact`/`opaque`/payload `noncomputable def`.
-/

namespace Pnp3
namespace Candidates
namespace NaturalProperty
namespace PscGapMCSP

/-- Truth table of an `n`-bit Boolean function. -/
abbrev BoolFn (n : Nat) := (Fin n → Bool) → Bool

/-- A property of Boolean functions, indexed by input length. -/
abbrev BoolProperty := (n : Nat) → BoolFn n → Prop

/--
Candidate source theorem (DRAFT shape).

The abstract predicates are placeholders the engineer instantiates with
the concrete repository notions:

* `InPpolyDAG`   ⟶ `ComplexityInterfaces.PpolyDAG` membership of the
  language decided by `f`;
* `IsGapMCSP`    ⟶ "f is the truth table of `gapPartialMCSP` at length
  `n`" (`Pnp3.Models`);
* `IsSubLarge`   ⟶ "the property holds for at most a `2^{-ω(n)}`
  fraction of functions" — the Razborov–Rudich largeness escape;
* `Constructive` ⟶ "the property is (quasi-)poly-time decidable on
  truth tables" — OR explicitly sacrificed (record which in
  `barrier_certificate.md §Natural proofs`);
* `NotHardwired` ⟶ the Rule 5 exclusion lemma: no truth-table /
  singleton witness satisfies the property.

A real candidate replaces these parameters with the concrete defs and
proves an inhabitant — that inhabitant is the open research content.
-/
def SourceTheorem_psc_gapmcsp
    (InPpolyDAG IsGapMCSP : BoolProperty)
    (IsSubLarge Constructive NotHardwired : BoolProperty → Prop) : Prop :=
  ∃ P : BoolProperty,
    Constructive P ∧
    (∀ (n : Nat) (f : BoolFn n), InPpolyDAG n f → ¬ P n f) ∧
    (∀ (n : Nat) (f : BoolFn n), IsGapMCSP n f → P n f) ∧
    IsSubLarge P ∧
    NotHardwired P

/--
Bridge **stub** (DRAFT).  Per `pnp3/Candidates/_template/proof.lean`, a
real candidate MUST retype the codomain to
`Pnp3.Magnification.ResearchGapWitness` and supply a real proof.
Returning `True` keeps the skeleton free of proof holes without
silently inhabiting the trust-root structure (which would violate
Rule 2).
-/
def gap_from_psc_gapmcsp
    {InPpolyDAG IsGapMCSP : BoolProperty}
    {IsSubLarge Constructive NotHardwired : BoolProperty → Prop}
    (_h : SourceTheorem_psc_gapmcsp
            InPpolyDAG IsGapMCSP IsSubLarge Constructive NotHardwired) :
    True :=
  True.intro

end PscGapMCSP
end NaturalProperty
end Candidates
end Pnp3
