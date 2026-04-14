/- 
Compatibility layer for the old `IsoStrongMain` experiment.

The historical version tried to build a concrete `IsoStrongFamilyEventually`
proof for `concreteFamily` directly.  In the active tree this object is still a
source-side obligation, not a closed theorem for the minimal family in
`mistral_test`.  To keep the library buildable without introducing axioms, this
module exposes the parameter choices and a named assumption surface.
-/
import MistralTestLib.SourceTheorems.ForcingProperty
import LowerBounds.AsymptoticDAGBarrierTheorems

namespace MistralTestLib

open Pnp3
open Pnp3.Models
open Pnp3.LowerBounds
open Pnp3.ComplexityInterfaces

/-- Compatibility value for the beta-threshold used in the old experiment. -/
def iso_beta0 : Rat := 1

/-- Compatibility coordinate budget from the original `mistral_test` route. -/
def iso_kappa (n : Nat) (_β : Rat) : Nat :=
  Partial.tableLen n / 2

/-- Eventual start index used by the concrete-family shim. -/
def iso_nIso (_β : Rat) : Nat :=
  concreteFamily.N0

/--
Named source obligation for the old concrete-family route.

This is the strongest statement the current `mistral_test` layer can expose
without adding a new proof beyond the active `pnp3` mainline.
-/
def ConcreteFamilyIsoStrongAssumption : Prop :=
  ∀ hInDag :
    ∀ n : Nat, ∀ β : Rat,
      ComplexityInterfaces.InPpolyDAG
        (gapPartialMCSP_Language (concreteFamily.paramsOf n β)),
      IsoStrongFamilyEventually concreteFamily hInDag

/-- Identity wrapper kept so downstream files can talk about the same source package. -/
theorem isoStrongFamilyEventually_theorem
    (hSrc : ConcreteFamilyIsoStrongAssumption) :
    ConcreteFamilyIsoStrongAssumption :=
  hSrc

/--
Compatibility alias for the family-level strong-isolation source obligation.

Unlike the historical file, this is intentionally a named `Prop`, not a closed
theorem: the unconditional witness is not present in the active tree.
-/
abbrev isoStrongFamilyEventually_concreteFamily : Prop :=
  ConcreteFamilyIsoStrongAssumption

end MistralTestLib
