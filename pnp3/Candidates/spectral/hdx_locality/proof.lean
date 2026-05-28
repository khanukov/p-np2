/-!
# Candidate `spectral / hdx_locality` — Lean skeleton

**Status: DRAFT SKELETON (not an intake-ready candidate; pending the
same §3-style audit that `natural_property/psc_gapmcsp` received).**

This file is **excluded from `lake build`** and is free of proof holes
so that Step 3 of `scripts/check.sh` stays green. Loaded only by
`scripts/verify_candidate.sh`.

Approach (see `sketch.md`): attack the **locality barrier** (B4, Chen et
al., JACM 2022 — the documented blocker of the repo's magnification
route). The locality barrier says weak lower-bound techniques survive
augmenting circuits with small-fan-in oracle gates. High-dimensional
expanders (HDX) are the science of *local-to-global*: extract a GLOBAL
hardness measure from local agreement/coboundary structure. The bet:
an HDX-derived measure can stay useful even against **oracle-extended**
poly-DAG circuits, which is exactly what beating B4 requires.

Engineer obligation: retype `gap_from_hdx_locality` from `→ True` to
`→ Pnp3.Magnification.ResearchGapWitness` and prove
"useful against oracle-extended P/poly ∧ holds on GapMCSP
⇒ ComplexityInterfaces.NP_not_subset_PpolyDAG".
-/

namespace Pnp3
namespace Candidates
namespace Spectral
namespace HdxLocality

/-- Truth table of an `n`-bit Boolean function. -/
abbrev BoolFn (n : Nat) := (Fin n → Bool) → Bool

/-- A property of Boolean functions, indexed by input length. -/
abbrev BoolProperty := (n : Nat) → BoolFn n → Prop

/--
Candidate source theorem (DRAFT shape). Abstract parameters:

* `InPpolyDAGOracle` ⟶ membership for poly-size DAG circuits **extended
  with small-fan-in oracle gates** — the locality-barrier model of Chen
  et al.; usefulness against THIS model is the B4 escape;
* `IsGapMCSP`        ⟶ "f is the `gapPartialMCSP` truth table at `n`";
* `GlobalHardness`   ⟶ an HDX local-to-global hardness measure on `P`;
* `NotHardwired`     ⟶ the Rule 5 exclusion lemma.

Note: usefulness is stated against the *oracle-extended* class on
purpose. Proving (2) for `InPpolyDAGOracle` (not merely plain
`PpolyDAG`) is precisely what the locality barrier forbids for local
techniques — so the inhabitant must be genuinely non-local.
-/
def SourceTheorem_hdx_locality
    (InPpolyDAGOracle IsGapMCSP : BoolProperty)
    (GlobalHardness NotHardwired : BoolProperty → Prop) : Prop :=
  ∃ P : BoolProperty,
    GlobalHardness P ∧
    (∀ (n : Nat) (f : BoolFn n), InPpolyDAGOracle n f → ¬ P n f) ∧
    (∀ (n : Nat) (f : BoolFn n), IsGapMCSP n f → P n f) ∧
    NotHardwired P

/--
Bridge **stub** (DRAFT). A real candidate MUST retype the codomain to
`Pnp3.Magnification.ResearchGapWitness` and supply a real proof
(usefulness even against the oracle-extended class gives the plain
`PpolyDAG` separation a fortiori). Returning `True` keeps the skeleton
free of proof holes without inhabiting the trust-root structure.
-/
def gap_from_hdx_locality
    {InPpolyDAGOracle IsGapMCSP : BoolProperty}
    {GlobalHardness NotHardwired : BoolProperty → Prop}
    (_h : SourceTheorem_hdx_locality
            InPpolyDAGOracle IsGapMCSP GlobalHardness NotHardwired) :
    True :=
  True.intro

/-!
## Current-shape no-go (auditor refutation, May 2026)

**Auditor verdict on the shape above:**
`RED_CURRENT_STATEMENT_ORACLE_TARGET_COLLISION`.

The arrow is reversed. Beating B4 requires usefulness against *plain*
`PpolyDAG` via a technique that does **not** extend to the oracle-
augmented class.  The shape above asks the opposite — usefulness against
the *oracle-extended* class — and the repo's `Docs/BARRIER_CATALOGUE.md`
records the B4 fact "Gap-MCSP admits highly-efficient circuits extended
with small-fan-in oracle gates".  Together these make the source
theorem **unconditionally False** as soon as `IsGapMCSP` is inhabited.

The theorem below formalises this: under the B4 fact (the third
hypothesis) and any inhabited `IsGapMCSP` slice (the second hypothesis),
the source theorem yields `False`.  This refutation IS the candidate's
deliverable; see `self_attack.md` Attack 8 (status `attack-succeeded`)
and `manifest.toml` (`status = "refuted"`).
-/

theorem hdx_locality_current_shape_impossible
    {InPpolyDAGOracle IsGapMCSP : BoolProperty}
    {GlobalHardness NotHardwired : BoolProperty → Prop}
    (hSource : SourceTheorem_hdx_locality
                  InPpolyDAGOracle IsGapMCSP GlobalHardness NotHardwired)
    (hGapInhabited : ∃ (n : Nat) (f : BoolFn n), IsGapMCSP n f)
    (hB4 : ∀ (n : Nat) (f : BoolFn n), IsGapMCSP n f → InPpolyDAGOracle n f) :
    False :=
  match hSource, hGapInhabited with
  | ⟨_P, _hGlobal, hUseful, hHolds, _hNotHardwired⟩, ⟨n, f, hGap⟩ =>
      hUseful n f (hB4 n f hGap) (hHolds n f hGap)

end HdxLocality
end Spectral
end Candidates
end Pnp3
