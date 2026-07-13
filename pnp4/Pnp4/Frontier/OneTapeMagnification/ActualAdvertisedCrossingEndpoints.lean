import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.ActualCrossingSegmentAlignment
import Pnp4.Frontier.OneTapeMagnification.AdvertisedCrossingEndpoints

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Advertised crossing endpoints agree with true chronological crossings

`AdvertisedCrossingEndpoints` determines a cut, direction, adjacent blocks,
and bounded work-head endpoints from arbitrary timed-alpha metadata.  This file
checks the completeness side for the metadata extracted from a concrete run:
every chronological entry reconstructs its actual physical cut, its forced
pre/post work heads equal the true crossing endpoints, and its advertised post
interface equals the true post-transition state and heads.

This is a per-crossing bridge.  It does not validate arbitrary decoded words,
chain neighboring tokens, construct all block visits, or check cut minimality.
-/

/-- A chronological entry's record occurs in the chronological record list. -/
theorem record_mem_chronologicalCanonicalCrossingRecords_of_entry_mem
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (entry : ChronologicalCanonicalCrossingEntry machine.State T b)
    (hentry : entry ∈
      chronologicalCanonicalCrossingEntries machine input T b hb) :
    entry.record ∈
      chronologicalCanonicalCrossingRecords machine input T b hb := by
  unfold chronologicalCanonicalCrossingRecords
  exact List.mem_map_of_mem hentry

/-- Reconstructing the timed entry's physical cut from the true alpha offsets
recovers its stored actual cut exactly. -/
theorem actualTimedEntry_advertisedPhysicalCut
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (entry : ChronologicalCanonicalCrossingEntry machine.State T b)
    (hentry : entry ∈
      chronologicalCanonicalCrossingEntries machine input T b hb) :
    advertisedTimedCrossingPhysicalCut
        (chronologicalTimedCanonicalAlpha machine input T b hb)
        (timedCanonicalCrossingTokenOfEntry entry) =
      entry.record.physicalCut := by
  have hrecovered :=
    mem_chronologicalCanonicalCrossingRecords_physicalCut_recovered
      machine input T b hb entry.record
      (record_mem_chronologicalCanonicalCrossingRecords_of_entry_mem
        machine input T b hb entry hentry)
  exact hrecovered.symm

/-- The head forced before the advertised crossing is the actual source head. -/
theorem actualTimedEntry_advertisedPreWorkHead
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (entry : ChronologicalCanonicalCrossingEntry machine.State T b)
    (hentry : entry ∈
      chronologicalCanonicalCrossingEntries machine input T b hb) :
    (advertisedTimedCrossingPreWorkHead
      (chronologicalTimedCanonicalAlpha machine input T b hb)
      (timedCanonicalCrossingTokenOfEntry entry)).val =
        (run machine input entry.time.val).workHead := by
  have hdata := mem_chronologicalCanonicalCrossingEntries_endpoint_data
    machine input T b hb entry hentry
  have hcut := actualTimedEntry_advertisedPhysicalCut
    machine input T b hb entry hentry
  have hcutVal := congrArg Fin.val hcut
  cases hdirection : entry.record.payload.direction
  · have hheads := hdata.2.2.2.2.1.mp hdirection
    simpa [advertisedTimedCrossingPreWorkHead,
      timedCanonicalCrossingTokenOfEntry,
      canonicalCrossingTokenOfRecord, hdirection] using
        hcutVal.trans hheads.1.symm
  · have hheads := hdata.2.2.2.2.2.mp hdirection
    have hcutSucc := congrArg (fun head => head + 1) hcutVal
    simpa [advertisedTimedCrossingPreWorkHead,
      timedCanonicalCrossingTokenOfEntry,
      canonicalCrossingTokenOfRecord, hdirection] using
        hcutSucc.trans hheads.1.symm

/-- The head forced after the advertised crossing is the actual post head. -/
theorem actualTimedEntry_advertisedPostWorkHead
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (entry : ChronologicalCanonicalCrossingEntry machine.State T b)
    (hentry : entry ∈
      chronologicalCanonicalCrossingEntries machine input T b hb) :
    (advertisedTimedCrossingPostWorkHead
      (chronologicalTimedCanonicalAlpha machine input T b hb)
      (timedCanonicalCrossingTokenOfEntry entry)).val =
        (run machine input (entry.time.val + 1)).workHead := by
  have hdata := mem_chronologicalCanonicalCrossingEntries_endpoint_data
    machine input T b hb entry hentry
  have hcut := actualTimedEntry_advertisedPhysicalCut
    machine input T b hb entry hentry
  have hcutVal := congrArg Fin.val hcut
  cases hdirection : entry.record.payload.direction
  · have hheads := hdata.2.2.2.2.1.mp hdirection
    have hcutSucc := congrArg (fun head => head + 1) hcutVal
    simpa [advertisedTimedCrossingPostWorkHead,
      timedCanonicalCrossingTokenOfEntry,
      canonicalCrossingTokenOfRecord, hdirection] using
        hcutSucc.trans hheads.2.symm
  · have hheads := hdata.2.2.2.2.2.mp hdirection
    simpa [advertisedTimedCrossingPostWorkHead,
      timedCanonicalCrossingTokenOfEntry,
      canonicalCrossingTokenOfRecord, hdirection] using
        hcutVal.trans hheads.2.symm

/-- The complete advertised finite post endpoint matches the actual state and
both head positions at the crossing's post-time.  It does not include the work
tape. -/
theorem actualTimedEntry_advertisedPostEndpoint_matches
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (entry : ChronologicalCanonicalCrossingEntry machine.State T b)
    (hentry : entry ∈
      chronologicalCanonicalCrossingEntries machine input T b hb) :
    ConfigurationMatchesFixedAlphaEndpoint
      (advertisedTimedCrossingPostEndpoint
        (chronologicalTimedCanonicalAlpha machine input T b hb)
        (timedCanonicalCrossingTokenOfEntry entry))
      (run machine input (entry.time.val + 1)) := by
  have hdata := mem_chronologicalCanonicalCrossingEntries_endpoint_data
    machine input T b hb entry hentry
  exact ⟨hdata.2.2.1,
    hdata.2.2.2.1,
    actualTimedEntry_advertisedPostWorkHead
      machine input T b hb entry hentry⟩

end OneTapeMagnification
end Frontier
end Pnp4
