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

/-!
## Structural critique (auditor, May 2026) — two kill-gates

The candidate's *shape* is correct (unlike `hdx_locality`'s reversed
arrow): usefulness is stated against plain `InPpolyDAG`. But the
deeper audit found that the candidate is **structurally hollow** in
two specific senses, both kernel-checked below.

### Gate A — sub-largeness is decorative (equivalence collapse)

The two main conjuncts of `SourceTheorem_psc_gapmcsp`
("useful against `InPpolyDAG`" + "holds on `IsGapMCSP`") together
are provably **equivalent** to the bare separation
`∀ n f, IsGapMCSP n f → ¬ InPpolyDAG n f`. The remaining conjuncts
(`Constructive`, `IsSubLarge`, `NotHardwired`) constrain the *form*
of the proof but do not reduce its mathematical content. In
particular, `IsSubLarge` is not load-bearing without a strong
`NotHardwired`: the witness `P := IsGapMCSP` itself satisfies
usefulness + accepts, and (under any natural largeness measure) is
already sub-large.

### Gate B — forbidden-target collision

If `IsGapMCSP` is instantiated to **any** target the repository
already proves to lie in `InPpolyDAG`, the source theorem is
unconditionally `False` (same structural shape as
`hdx_locality_current_shape_impossible`, against plain `InPpolyDAG`
rather than oracle-extended).

Repo-proved DAG-hardwirings the engineer must therefore **forbid**
as `IsGapMCSP` instantiations:

* `Tests.HInDagTrivialityProbe.fixedSlice_gapPartialMCSP_in_PpolyDAG`
  — fixed-slice `gapPartialMCSP_Language p` is in `PpolyDAG` via
  per-slice truth-table hardwiring at constant `K_p`;
* `Tests.HInDagTrivialityProbe.hInDag_for_canonicalAsymptoticHAsym`
  — canonical asymptotic GapMCSP (`sYES=1, sNO=2`) is in `PpolyDAG`
  for the same reason; the canonical track is additionally refuted
  at conclusion level (`STATUS.md §Audit chain stages 11, 14`).

A valid C1 instantiation requires a **new** asymptotic NP language
that is (i) not yet repo-hardwirable, and (ii) where no analogous
truth-table-hardwiring witness should be derivable. Picking such a
language is itself an open design question, recorded as the
engineer-blocking precondition.
-/

/-- **Gate A.** Sub-largeness is decorative: the two main structural
conjuncts of `SourceTheorem_psc_gapmcsp` together are equivalent to
the bare DAG separation `IsGapMCSP ⇒ ¬ InPpolyDAG`. -/
theorem psc_two_conjuncts_iff_bare_separation
    (InPpolyDAG IsGapMCSP : BoolProperty) :
    (∃ P : BoolProperty,
        (∀ (n : Nat) (f : BoolFn n), InPpolyDAG n f → ¬ P n f) ∧
        (∀ (n : Nat) (f : BoolFn n), IsGapMCSP n f → P n f))
    ↔
    (∀ (n : Nat) (f : BoolFn n), IsGapMCSP n f → ¬ InPpolyDAG n f) :=
  Iff.intro
    (fun hExists n f hGap hInPpoly =>
      match hExists with
      | ⟨_P, hUseful, hHolds⟩ => hUseful n f hInPpoly (hHolds n f hGap))
    (fun hSep =>
      ⟨IsGapMCSP,
       fun n f hInPpoly hGap => hSep n f hGap hInPpoly,
       fun _ _ hGap => hGap⟩)

/-- **Gate B.** Forbidden-target collapse. If the chosen `IsGapMCSP`
predicate identifies a target the repository already proves to lie in
`InPpolyDAG` (e.g. `fixedSlice_gapPartialMCSP_in_PpolyDAG` or
`hInDag_for_canonicalAsymptoticHAsym`), the source theorem is
unconditionally `False`. -/
theorem psc_forbidden_target_collapse
    {InPpolyDAG IsGapMCSP : BoolProperty}
    {IsSubLarge Constructive NotHardwired : BoolProperty → Prop}
    (hSource : SourceTheorem_psc_gapmcsp
                  InPpolyDAG IsGapMCSP IsSubLarge Constructive NotHardwired)
    (hGapInhabited : ∃ (n : Nat) (f : BoolFn n), IsGapMCSP n f)
    (hTargetInPpoly :
      ∀ (n : Nat) (f : BoolFn n), IsGapMCSP n f → InPpolyDAG n f) :
    False :=
  match hSource, hGapInhabited with
  | ⟨_P, _hConstr, hUseful, hHolds, _hSub, _hNH⟩, ⟨n, f, hGap⟩ =>
      hUseful n f (hTargetInPpoly n f hGap) (hHolds n f hGap)

end PscGapMCSP
end NaturalProperty
end Candidates
end Pnp3
