/- 
Compatibility shim for the old `ForcingProperty` experiment.

The original file attempted to prove a custom table-support forcing lemma
directly against an older DAG API.  The active `pnp3` tree now exposes that
logic through the generic weak-route interfaces in
`LowerBounds.AsymptoticDAGBarrierInterfaces` and
`LowerBounds.DAGStableRestrictionProducer`.  For `mistral_test` we keep a small
surface module so the library still builds while the real forcing route lives in
the main tree.
-/
import MistralTestLib.SourceTheorems.ConcreteFamily
import LowerBounds.AsymptoticDAGBarrierInterfaces
import LowerBounds.DAGStableRestrictionProducer

namespace MistralTestLib.ForcingProperty

open Pnp3
open Pnp3.Models
open Pnp3.LowerBounds
open Pnp3.ComplexityInterfaces

/-- Semantic table-coordinate carrier used by the weak-route interfaces. -/
abbrev TableCoordinateSet (p : GapPartialMCSPParams) :=
  Finset (Fin (Partial.tableLen p.n))

/-- Encoded input length for one concrete gap-Partial-MCSP slice. -/
abbrev EncodedLen (p : GapPartialMCSPParams) : Nat :=
  partialInputLen p

/-- Promise slice attached to one concrete parameter package. -/
abbrev PromiseSlice (p : GapPartialMCSPParams) :=
  gapSliceOfParams p

/--
Compatibility alias for the current semantic coordinate witness package.

This is the nearest active-tree replacement for the older bespoke
`support_on_table`/forcing layer.
-/
abbrev PromiseYesCertificateAt
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {ε : Rat}
    (W : SmallDAGWitnessOnSlice p SizeBound ε) :=
  PromiseYesSubcubeCertificateAt W

end MistralTestLib.ForcingProperty
