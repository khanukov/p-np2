import Tests.GeneralIsoStrongNoGoProbe
import Tests.HInDagTrivialityProbe
import Magnification.FinalResultMainline
import Magnification.CanonicalAsymptoticTrackData

/-!
# General iso-strong route closure (named theorem packaging)

This test-local file packages the strategic consequences of
`isoStrong_conclusion_negative_general`
(`pnp3/Tests/GeneralIsoStrongNoGoProbe.lean`) as small named theorems
that explicitly close the iso-strong, promise-YES certificate, and
promise-YES weak route props at the canonical asymptotic
instantiation.

These theorems do **not** construct `P ≠ NP` or any unconditional
lower bound.  Each is a direct corollary of theorems already on
`main`:

- `isoStrong_conclusion_negative_general` (per-`hInDag` refutation),
- `HInDagTrivialityProbe.hInDag_for_canonicalAsymptoticHAsym`
  (concrete per-slice truth-table hardwiring witness from L0),
- `asymptoticIsoStrongRoute_of_asymptoticPromiseYesCertificateRoute`
  and `asymptoticPromiseYesCertificateRoute_of_asymptoticPromiseYesWeakRouteEventually`
  (pointwise bridge implications from
  `pnp3/Magnification/FinalResultMainline.lean`).

## Why these theorems exist

The bare statement `isoStrong_conclusion_negative_general` says
`∀ F hInDag, ¬ IsoStrongFamilyEventually F hInDag` but does not
explicitly translate this into the corresponding **route-level**
emptiness claims.  Without the named corollaries below, a future
reader can encounter `AsymptoticIsoStrongRoute` or
`AsymptoticPromiseYesCertificateRoute` in the route catalogue and
mistakenly treat them as surviving, since their refutation is
only available as a meta-argument rather than a packaged theorem.

This file fixes that by recording the four named closures:

- `not_AsymptoticIsoStrongRoute_of_hInDag` (parameter-agnostic);
- `not_AsymptoticIsoStrongRoute_canonical`;
- `not_AsymptoticPromiseYesCertificateRoute_canonical`;
- `not_AsymptoticPromiseYesWeakRouteEventually_canonical`.

This file is local to `pnp3/Tests/` and does not modify endpoints,
specs, or trust-root surfaces.  No kernel-incomplete proof
placeholders or escape hatches are introduced (the file is checked
by `./scripts/check.sh` Step 3/17 source-hygiene scan).
-/

namespace Pnp3
namespace Tests
namespace GeneralIsoStrongRouteClosure

open Magnification
open Models
open ComplexityInterfaces

/--
Parameter-agnostic helper: under any per-slice `InPpolyDAG` witness
family for the slice-family induced by `hAsym`, the iso-strong route
prop is empty.

This is the direct route-level translation of
`isoStrong_conclusion_negative_general`: instantiate the universal
`AsymptoticIsoStrongRoute` consumer at the supplied `hInDag` and
discharge the resulting `IsoStrongFamilyEventually` against the
generic refutation.
-/
theorem not_AsymptoticIsoStrongRoute_of_hInDag
    (hAsym : AsymptoticFormulaTrackHypothesis)
    (hInDag :
      ∀ n β,
        ComplexityInterfaces.InPpolyDAG
          (gapPartialMCSP_Language
            ((eventualGapSliceFamily_of_asymptotic hAsym).paramsOf n β))) :
    ¬ AsymptoticIsoStrongRoute hAsym := by
  intro hRoute
  exact GeneralIsoStrongNoGoProbe.isoStrong_conclusion_negative_general
    (eventualGapSliceFamily_of_asymptotic hAsym)
    hInDag
    (hRoute hInDag)

/--
Canonical specialisation: at `canonicalAsymptoticHAsym` the iso-strong
route prop is empty, witnessed concretely by
`HInDagTrivialityProbe.hInDag_for_canonicalAsymptoticHAsym` (per-slice
truth-table hardwiring witness landed in L0 #1388).
-/
theorem not_AsymptoticIsoStrongRoute_canonical :
    ¬ AsymptoticIsoStrongRoute canonicalAsymptoticHAsym :=
  not_AsymptoticIsoStrongRoute_of_hInDag
    canonicalAsymptoticHAsym
    HInDagTrivialityProbe.hInDag_for_canonicalAsymptoticHAsym

/--
Canonical promise-YES certificate route is empty.  Direct corollary
of `not_AsymptoticIsoStrongRoute_canonical` via the existing
pointwise bridge `asymptoticIsoStrongRoute_of_asymptoticPromiseYesCertificateRoute`
(`pnp3/Magnification/FinalResultMainline.lean:400`).
-/
theorem not_AsymptoticPromiseYesCertificateRoute_canonical :
    ¬ AsymptoticPromiseYesCertificateRoute canonicalAsymptoticHAsym := by
  intro hRoute
  exact not_AsymptoticIsoStrongRoute_canonical
    (asymptoticIsoStrongRoute_of_asymptoticPromiseYesCertificateRoute
      canonicalAsymptoticHAsym hRoute)

/--
Canonical promise-YES weak (eventual) route is empty.  Direct corollary
of `not_AsymptoticPromiseYesCertificateRoute_canonical` via the
existing pointwise bridge
`asymptoticPromiseYesCertificateRoute_of_asymptoticPromiseYesWeakRouteEventually`
(`pnp3/Magnification/FinalResultMainline.lean:348`).
-/
theorem not_AsymptoticPromiseYesWeakRouteEventually_canonical :
    ¬ AsymptoticPromiseYesWeakRouteEventually canonicalAsymptoticHAsym := by
  intro hWeak
  exact not_AsymptoticPromiseYesCertificateRoute_canonical
    (asymptoticPromiseYesCertificateRoute_of_asymptoticPromiseYesWeakRouteEventually
      canonicalAsymptoticHAsym hWeak)

end GeneralIsoStrongRouteClosure
end Tests
end Pnp3
