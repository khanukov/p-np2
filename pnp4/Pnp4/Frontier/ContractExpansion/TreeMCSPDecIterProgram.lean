import Pnp4.Frontier.ContractExpansion.TreeMCSPRemWalk

/-!
# `decIterProgram` — D2t-5b (Block A5m-4, machine): the settle-dec iteration as a region union

One full **dec** iteration of the driver: from the settle home at the cursor marker, navigate to
the control top, read the tag (`ctrlTopWalk`) and the remaining count (`remWalk`, dec verdict),
rewrite the top frame in place (`writeBits` of `encodeCtrlFrameR (tag, 1) ++ [false]` from the frame
base — exactly `corridorInv_decStep`'s transformer), and scan home.  Branching is by regions: the
three tag verdicts route to three per-tag `remWalk` copies, whose dec verdicts route to the three
per-tag write regions, all converging on the shared return scan.  Non-dec verdicts (empty / pop /
rejects) route to the designated `stuck` phase — this staging machine handles exactly the dec
branch (the full driver routes those exits to the other arms).

Phase layout (`N = 69`): `0–1` stepLeft · `2–3` scanLeft · `4–13` ctrlTopWalk (empty ↦ 68, tnot ↦
14, tand ↦ 22, tor ↦ 30, reject ↦ 68) · `14–21`/`22–29`/`30–37` remWalk per tag (pop ↦ 68, dec ↦
the tag's write region, reject ↦ 68) · `38–45`/`46–54`/`55–64` writeBits per tag (↦ 65) · `65–66`
scanRight (↦ 67) · `67` home-read out · `68` stuck.

**Progress classification (AGENTS.md): Infrastructure** — a staging machine and its region
contracts; proves no separation.  Standard `[propext, Classical.choice, Quot.sound]` triple only.
**No `P ≠ NP` claim.** -/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram
open Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-- The dec frame blocks: the rewritten `(tag, 1)` frame plus the one-cell pad. -/
def decBlock (tag : ITag) : List Bool := encodeCtrlFrameR (tag, 1) ++ [false]

@[simp] theorem decBlock_length (tag : ITag) : (decBlock tag).length = tag.tagCode + 7 := by
  simp [decBlock, encodeCtrlFrameR_length]
  omega

/-- The ctrlTopWalk redirect map of the dec machine. -/
def decCtrlTopRedirect : Nat → Option Nat :=
  fun j => if j = 5 then some 68 else if j = 6 then some 14 else if j = 7 then some 22
    else if j = 8 then some 30 else if j = 9 then some 68 else none

/-- The per-tag remWalk redirect maps (pop ↦ stuck, dec ↦ the tag's write region). -/
def decRemRedirect (wbase : Nat) : Nat → Option Nat :=
  fun j => if j = 5 then some 68 else if j = 6 then some wbase else if j = 7 then some 68
    else none

/-- The dec-iteration phase assignment (see the layout table in the module docstring). -/
def decIterAssign : Nat → RegionAction := fun i =>
  if i < 2 then .run stepLeftOnce 0 (i - 0) (fun j => if j = 1 then some 2 else none)
  else if i < 4 then .run selfLoopScanLeft 2 (i - 2) (fun j => if j = 1 then some 4 else none)
  else if i < 14 then .run ctrlTopWalk 4 (i - 4) decCtrlTopRedirect
  else if i < 22 then .run remWalk 14 (i - 14) (decRemRedirect 38)
  else if i < 30 then .run remWalk 22 (i - 22) (decRemRedirect 46)
  else if i < 38 then .run remWalk 30 (i - 30) (decRemRedirect 55)
  else if i < 46 then .run (writeBits (decBlock ITag.tnot)) 38 (i - 38)
    (fun j => if j = 7 then some 65 else none)
  else if i < 55 then .run (writeBits (decBlock ITag.tand)) 46 (i - 46)
    (fun j => if j = 8 then some 65 else none)
  else if i < 65 then .run (writeBits (decBlock ITag.tor)) 55 (i - 55)
    (fun j => if j = 9 then some 65 else none)
  else if i < 67 then .run gammaSelfLoopScan 65 (i - 65) (fun j => if j = 1 then some 67 else none)
  else .idle

/-- **The settle-dec iteration machine** (69 phases; start at the settle home `0`, nominal accept
at the home-read out `67`). -/
def decIterProgram : ConstStatePhasedProgram Unit :=
  unionProgram 69 (by omega) ⟨0, by omega⟩ ⟨67, by omega⟩ decIterAssign

/-! ### The region contracts (one instantiation each) -/

theorem decIter_region_stepLeft :
    RegionEmbedded decIterProgram stepLeftOnce 0 2 := by
  refine RegionEmbeddedMulti.toSingle ?_
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [stepLeftOnce]) ?_
  · intro k hk
    have hk' : k < 2 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    split at h
    · cases h; omega
    · cases h

theorem decIter_region_scanLeft :
    RegionEmbedded decIterProgram selfLoopScanLeft 2 4 := by
  refine RegionEmbeddedMulti.toSingle ?_
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [selfLoopScanLeft]) ?_
  · intro k hk
    have hk' : k < 2 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    split at h
    · cases h; omega
    · cases h

theorem decIter_region_ctrlTopWalk :
    RegionEmbeddedMulti decIterProgram ctrlTopWalk 4 decCtrlTopRedirect := by
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [ctrlTopWalk]) ?_
  · intro k hk
    have hk' : k < 10 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold decCtrlTopRedirect at h
    split at h
    · cases h; omega
    · split at h
      · cases h; omega
      · split at h
        · cases h; omega
        · split at h
          · cases h; omega
          · split at h
            · cases h; omega
            · cases h

theorem decIter_region_remWalkNot :
    RegionEmbeddedMulti decIterProgram remWalk 14 (decRemRedirect 38) := by
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [remWalk]) ?_
  · intro k hk
    have hk' : k < 8 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold decRemRedirect at h
    split at h
    · cases h; omega
    · split at h
      · cases h; omega
      · split at h
        · cases h; omega
        · cases h

theorem decIter_region_remWalkAnd :
    RegionEmbeddedMulti decIterProgram remWalk 22 (decRemRedirect 46) := by
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [remWalk]) ?_
  · intro k hk
    have hk' : k < 8 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold decRemRedirect at h
    split at h
    · cases h; omega
    · split at h
      · cases h; omega
      · split at h
        · cases h; omega
        · cases h

theorem decIter_region_remWalkOr :
    RegionEmbeddedMulti decIterProgram remWalk 30 (decRemRedirect 55) := by
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [remWalk]) ?_
  · intro k hk
    have hk' : k < 8 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold decRemRedirect at h
    split at h
    · cases h; omega
    · split at h
      · cases h; omega
      · split at h
        · cases h; omega
        · cases h

theorem decIter_region_writeNot :
    RegionEmbedded decIterProgram (writeBits (decBlock ITag.tnot)) 38 65 := by
  have hacc : ((writeBits (decBlock ITag.tnot)).acceptPhase : Nat) = 7 := by
    simp [decBlock_length, ITag.tagCode]
  refine RegionEmbeddedMulti.toSingle ?_
  rw [show (fun j => if j = ((writeBits (decBlock ITag.tnot)).acceptPhase : Nat)
      then some 65 else none) = (fun j => if j = 7 then some 65 else none) from by
    funext j; rw [hacc]]
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_
    (by simp only [unionProgram_numPhases, writeBits_numPhases, decBlock_length, ITag.tagCode]
        omega) ?_
  · intro k hk
    have hk' : k < 8 := by
      have := hk
      simp only [writeBits_numPhases, decBlock_length, ITag.tagCode] at this
      omega
    interval_cases k <;> rfl
  · intro j nxt h
    split at h
    · cases h; omega
    · cases h

theorem decIter_region_writeAnd :
    RegionEmbedded decIterProgram (writeBits (decBlock ITag.tand)) 46 65 := by
  have hacc : ((writeBits (decBlock ITag.tand)).acceptPhase : Nat) = 8 := by
    simp [decBlock_length, ITag.tagCode]
  refine RegionEmbeddedMulti.toSingle ?_
  rw [show (fun j => if j = ((writeBits (decBlock ITag.tand)).acceptPhase : Nat)
      then some 65 else none) = (fun j => if j = 8 then some 65 else none) from by
    funext j; rw [hacc]]
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_
    (by simp only [unionProgram_numPhases, writeBits_numPhases, decBlock_length, ITag.tagCode]
        omega) ?_
  · intro k hk
    have hk' : k < 9 := by
      have := hk
      simp only [writeBits_numPhases, decBlock_length, ITag.tagCode] at this
      omega
    interval_cases k <;> rfl
  · intro j nxt h
    split at h
    · cases h; omega
    · cases h

theorem decIter_region_writeOr :
    RegionEmbedded decIterProgram (writeBits (decBlock ITag.tor)) 55 65 := by
  have hacc : ((writeBits (decBlock ITag.tor)).acceptPhase : Nat) = 9 := by
    simp [decBlock_length, ITag.tagCode]
  refine RegionEmbeddedMulti.toSingle ?_
  rw [show (fun j => if j = ((writeBits (decBlock ITag.tor)).acceptPhase : Nat)
      then some 65 else none) = (fun j => if j = 9 then some 65 else none) from by
    funext j; rw [hacc]]
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_
    (by simp only [unionProgram_numPhases, writeBits_numPhases, decBlock_length, ITag.tagCode]
        omega) ?_
  · intro k hk
    have hk' : k < 10 := by
      have := hk
      simp only [writeBits_numPhases, decBlock_length, ITag.tagCode] at this
      omega
    interval_cases k <;> rfl
  · intro j nxt h
    split at h
    · cases h; omega
    · cases h

theorem decIter_region_scanRight :
    RegionEmbedded decIterProgram gammaSelfLoopScan 65 67 := by
  refine RegionEmbeddedMulti.toSingle ?_
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [gammaSelfLoopScan]) ?_
  · intro k hk
    have hk' : k < 2 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    split at h
    · cases h; omega
    · cases h

end ContractExpansion
end Frontier
end Pnp4
