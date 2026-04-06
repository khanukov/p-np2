import Complexity.Interfaces
import Complexity.Promise
import Models.Model_PartialMCSP
import LowerBounds.AcceptedFamilyBarrier
import LowerBounds.MCSPGapLocality
import Mathlib.Data.Finset.Card

namespace Pnp3
namespace LowerBounds

open ComplexityInterfaces
open Complexity
open Models

/-- Canonical asymptotic Gap-PartialMCSP language used by magnification layer. -/
noncomputable abbrev AsymptoticGapLanguage := gapPartialMCSP_AsymptoticLanguage

/-- Agreement of two inputs on a coordinate set `S`. -/
def AgreeOn {N : Nat} (S : Finset (Fin N)) (x y : Bitstring N) : Prop :=
  ∀ i ∈ S, x i = y i

/-- Promise slice at one concrete encoded input length `N`. -/
structure GapSlice (N : Nat) where
  Yes : Set (Bitstring N)
  No : Set (Bitstring N)

/-- Semantic correctness of a DAG circuit on one promise slice. -/
def CorrectOnPromiseSlice {N : Nat} (C : DagCircuit N) (P : GapSlice N) : Prop :=
  (∀ x, x ∈ P.Yes → DagCircuit.eval C x = true) ∧
  (∀ x, x ∈ P.No → DagCircuit.eval C x = false)

/-- Slice extracted from fixed `GapPartialMCSPParams`. -/
def gapSliceOfParams (p : GapPartialMCSPParams) : GapSlice (partialInputLen p) where
  Yes := {x | gapPartialMCSP_Language p (partialInputLen p) x = true}
  No := {x | gapPartialMCSP_Language p (partialInputLen p) x = false}

/-- Auxiliary guard-rail only (not the primary endpoint schema). -/
def InfinitelyOftenNontrivial (L : Language) : Prop :=
  ∀ N0 : Nat, ∃ n ≥ N0, ∃ x y : Bitstring n, L n x ≠ L n y

/--
Structured `(n,β)` slice family used by all theorem-level barrier statements.

`hIndex`, `hT`, `hM` are intentional *coherence fields* packed into one object,
so downstream theorems consume a single argument `F` instead of transport data
spread across theorem signatures.
-/
structure GapSliceFamily where
  paramsOf : Nat → Rat → GapPartialMCSPParams
  Tof : Nat → Rat → Nat
  Mof : Nat → Nat → Nat
  hIndex : ∀ n : Nat, ∀ β : Rat, (paramsOf n β).n = n
  hT : ∀ n : Nat, ∀ β : Rat, Tof n β = (paramsOf n β).sNO - 1
  hM : ∀ n : Nat, ∀ T : Nat, Mof n T = Models.circuitCountBound n T

/-
The legacy `GapSliceFamily` carrier is intentionally kept for compatibility with
historical theorem surfaces.  Its emptiness proof and vacuity corollaries are
separated into `LowerBounds.FailedRoute_GapSliceFamilyVacuous`.
-/

/--
Eventual (non-vacuous) replacement for `GapSliceFamily`.

The key difference is that coherence obligations are only required on
indices `n ≥ N0`.  This matches the asymptotic style already used in other
parts of the development and avoids the `n = 0` contradiction that makes
`GapSliceFamily` empty.
-/
structure GapSliceFamilyEventually where
  /-- Start index of the asymptotic regime. -/
  N0 : Nat
  /-- Slice parameters indexed by `(n, β)`. -/
  paramsOf : Nat → Rat → GapPartialMCSPParams
  /-- Canonical threshold selector. -/
  Tof : Nat → Rat → Nat
  /-- Counting upper bound selector. -/
  Mof : Nat → Nat → Nat
  /--
  Index coherence, required only eventually.

  For every `n ≥ N0`, the selected parameter object is aligned with this same
  `n`.  This is the exact field that was previously inconsistent at `n = 0`.
  -/
  hIndex :
    ∀ n : Nat, N0 ≤ n → ∀ β : Rat, (paramsOf n β).n = n
  /-- Threshold coherence, required only eventually. -/
  hT :
    ∀ n : Nat, N0 ≤ n → ∀ β : Rat, Tof n β = (paramsOf n β).sNO - 1
  /-- Counting coherence, required only eventually. -/
  hM :
    ∀ n : Nat, N0 ≤ n → ∀ T : Nat, Mof n T = Models.circuitCountBound n T

namespace GapSliceFamilyEventually

/-- Encoded-input coordinate length for one eventual slice `(n,β)`. -/
def encodedLen (F : GapSliceFamilyEventually) (n : Nat) (β : Rat) : Nat :=
  partialInputLen (F.paramsOf n β)

/-- Truth-table coordinate length for one eventual slice `(n,β)`. -/
def tableLen (F : GapSliceFamilyEventually) (n : Nat) (β : Rat) : Nat :=
  Partial.tableLen (F.paramsOf n β).n

end GapSliceFamilyEventually

/--
Length-local bridge from one global language to eventual fixed slices.

This intentionally weakens the previous all-length bridge surface:
agreement is demanded only on the target encoded length of each slice, not on
every input length simultaneously.
-/
structure AsymptoticDAGSliceBridgeAt (F : GapSliceFamilyEventually) : Type where
  /-- One global language used by the asymptotic route. -/
  L : Language
  /--
  Slice agreement on the encoded length of `(n,β)`.

  This is the only equality needed to transfer a global witness to a concrete
  slice.
  -/
  sliceEq :
    ∀ n : Nat, F.N0 ≤ n → ∀ β : Rat,
      ∀ x : Bitstring (GapSliceFamilyEventually.encodedLen F n β),
        L (GapSliceFamilyEventually.encodedLen F n β) x =
          gapPartialMCSP_Language (F.paramsOf n β)
            (GapSliceFamilyEventually.encodedLen F n β) x

namespace GapSliceFamily

/-- Encoded-input coordinate length (`mask ++ values`) for slice `(n,β)`. -/
def encodedLen (F : GapSliceFamily) (n : Nat) (β : Rat) : Nat :=
  partialInputLen (F.paramsOf n β)

/-- Truth-table coordinate length for slice `(n,β)`. -/
def tableLen (F : GapSliceFamily) (n : Nat) (β : Rat) : Nat :=
  Partial.tableLen (F.paramsOf n β).n

/--
Counting slack used in certificates.

Important note (to avoid future confusion):
* `S` lives on encoded-input coordinates (`encodedLen = 2 * 2^n`),
* exponent uses truth-table length (`tableLen = 2^n`).

So this is a deliberately strong condition comparing table-level entropy budget
against alive encoded coordinates.
-/
def tableSlack (F : GapSliceFamily) (n : Nat) (β : Rat)
    (S : Finset (Fin (encodedLen F n β))) : Nat :=
  tableLen F n β - S.card

end GapSliceFamily

/-- Layer A (counting anti-locality) at one concrete slice `(n,β)`. -/
def GapAntiLocalityAt (F : GapSliceFamily) (n : Nat) (β : Rat) : Prop :=
  ∀ S : Finset (Fin (GapSliceFamily.encodedLen F n β)),
    F.Mof n (F.Tof n β) < 2 ^ (GapSliceFamily.tableSlack F n β S) →
      ∃ x y : Bitstring (GapSliceFamily.encodedLen F n β),
        AgreeOn S x y ∧ y ∈ (gapSliceOfParams (F.paramsOf n β)).Yes ∧
        x ∈ (gapSliceOfParams (F.paramsOf n β)).No

/-- Layer A for the whole family. -/
def GapAntiLocalityStatement (F : GapSliceFamily) : Prop :=
  ∀ n : Nat, ∀ β : Rat, GapAntiLocalityAt F n β

/-- Language-level locality at one concrete slice `(n,β)`. -/
def SliceLanguageLocalityAt (F : GapSliceFamily) (n : Nat) (β : Rat) : Prop :=
  ∃ S : Finset (Fin (GapSliceFamily.encodedLen F n β)),
    F.Mof n (F.Tof n β) < 2 ^ (GapSliceFamily.tableSlack F n β S) ∧
    ∀ x y : Bitstring (GapSliceFamily.encodedLen F n β),
      AgreeOn S x y →
        gapPartialMCSP_Language (F.paramsOf n β) (GapSliceFamily.encodedLen F n β) x =
        gapPartialMCSP_Language (F.paramsOf n β) (GapSliceFamily.encodedLen F n β) y

/-- Language-level locality for all slices. -/
def SliceLanguageLocalityStatement (F : GapSliceFamily) : Prop :=
  ∀ n : Nat, ∀ β : Rat, SliceLanguageLocalityAt F n β

/-- Layer B (solver-level locality) at one concrete slice `(n,β)`. -/
def SmallDAGImpliesCoordinateLocalityAt
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (n : Nat) (β ε : Rat) : Prop :=
  ∀ C : DagCircuit (GapSliceFamily.encodedLen F n β),
    SizeBound n β ε (DagCircuit.size C) →
    CorrectOnPromiseSlice C (gapSliceOfParams (F.paramsOf n β)) →
      ∃ S : Finset (Fin (GapSliceFamily.encodedLen F n β)),
        F.Mof n (F.Tof n β) < 2 ^ (GapSliceFamily.tableSlack F n β S) ∧
        ∀ x y : Bitstring (GapSliceFamily.encodedLen F n β),
          AgreeOn S x y → DagCircuit.eval C x = DagCircuit.eval C y

/--
Promise/value version of Layer B at one concrete slice `(n,β)`.

This interface only asks for locality on canonical encoded inputs lying on the
promise domain, and only with respect to semantic truth-table value bits.
-/
def SmallDAGImpliesPromiseValueLocalityAt
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (n : Nat) (β ε : Rat) : Prop :=
  let p := F.paramsOf n β
  ∀ C : DagCircuit (GapSliceFamily.encodedLen F n β),
    SizeBound n β ε (DagCircuit.size C) →
    CorrectOnPromiseSlice C (gapSliceOfParams p) →
      ∃ S : Finset (Fin (GapSliceFamily.tableLen F n β)),
        F.Mof n (F.Tof n β) < 2 ^ (GapSliceFamily.tableLen F n β - S.card) ∧
        ∀ x y : Bitstring (GapSliceFamily.encodedLen F n β),
          x ∈ (gapSliceOfParams p).Yes →
          y ∈ (gapSliceOfParams p).No →
          ValidEncoding p x →
          ValidEncoding p y →
          AgreeOnValues (p := p) S x y →
            DagCircuit.eval C x = DagCircuit.eval C y

/-- Promise/value version of Layer B for the whole family. -/
def SmallDAGImpliesPromiseValueLocalityStatement
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop) : Prop :=
  ∀ n : Nat, ∀ β ε : Rat, SmallDAGImpliesPromiseValueLocalityAt F SizeBound n β ε

/--
One-sided YES-centered promise/value version of Layer B at one concrete slice
`(n,β)`.

This is the nearest-term weak-route source theorem target: instead of demanding
pairwise locality across YES/NO pairs, the solver only needs to accept every
valid promise-relevant completion around one concrete YES center on a small
semantic coordinate set.
-/
def SmallDAGImpliesPromiseYesSubcubeAt
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (n : Nat) (β ε : Rat) : Prop :=
  let p := F.paramsOf n β
  ∀ C : DagCircuit (GapSliceFamily.encodedLen F n β),
    SizeBound n β ε (DagCircuit.size C) →
    CorrectOnPromiseSlice C (gapSliceOfParams p) →
      ∃ yYes : Bitstring (GapSliceFamily.encodedLen F n β),
        yYes ∈ (gapSliceOfParams p).Yes ∧
        ValidEncoding p yYes ∧
        ∃ S : Finset (Fin (GapSliceFamily.tableLen F n β)),
          F.Mof n (F.Tof n β) < 2 ^ (GapSliceFamily.tableLen F n β - S.card) ∧
          ∀ z : Bitstring (GapSliceFamily.encodedLen F n β),
            (z ∈ (gapSliceOfParams p).Yes ∨ z ∈ (gapSliceOfParams p).No) →
            ValidEncoding p z →
            AgreeOnValues (p := p) S yYes z →
              DagCircuit.eval C z = true

/-- One-sided YES-centered promise/value version of Layer B for the whole family. -/
def SmallDAGImpliesPromiseYesSubcubeStatement
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop) : Prop :=
  ∀ n : Nat, ∀ β ε : Rat, SmallDAGImpliesPromiseYesSubcubeAt F SizeBound n β ε

/--
Accepted-family version of Layer B at one concrete slice `(n,β)`.

This is the new theorem-minimal weak endpoint: a small correct DAG solver on
the current slice must come with some accepted family of valid truth tables
whose size already exceeds the counting capacity threshold.
-/
def SmallDAGImpliesAcceptedFamilyAt
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop)
    (n : Nat) (β ε : Rat) : Prop :=
  let p := F.paramsOf n β
  ∀ C : DagCircuit (GapSliceFamily.encodedLen F n β),
    SizeBound n β ε (DagCircuit.size C) →
    CorrectOnPromiseSlice C (gapSliceOfParams p) →
      Nonempty (AcceptedFamilyCertificate (p := p) (DagCircuit.eval C))

/-- Accepted-family version of Layer B for the whole family. -/
def SmallDAGImpliesAcceptedFamilyStatement
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop) : Prop :=
  ∀ n : Nat, ∀ β ε : Rat, SmallDAGImpliesAcceptedFamilyAt F SizeBound n β ε

/-- Layer B for the whole family. -/
def SmallDAGImpliesCoordinateLocalityStatement
    (F : GapSliceFamily)
    (SizeBound : Nat → Rat → Rat → Nat → Prop) : Prop :=
  ∀ n : Nat, ∀ β ε : Rat, SmallDAGImpliesCoordinateLocalityAt F SizeBound n β ε


end LowerBounds
end Pnp3
