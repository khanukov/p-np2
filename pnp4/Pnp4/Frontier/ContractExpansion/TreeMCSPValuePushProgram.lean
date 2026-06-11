import Pnp4.Frontier.ContractExpansion.TreeMCSPRegionOnesScanHops
import Pnp4.Frontier.ContractExpansion.TreeMCSPRegionUnion
import Pnp4.Frontier.ContractExpansion.TreeMCSPRegionWriteSegment
import Pnp4.Frontier.ContractExpansion.TreeMCSPRegionAtomHops
import Pnp4.Frontier.ContractExpansion.TreeMCSPClearIterProgram
import Pnp4.Frontier.ContractExpansion.TreeMCSPNodeIterProgram

/-!
# `valuePushProgram` — D2t-6b (M1 / A5m-V, machine): the non-destructive count duplicator

The value-push primitive: from the home anchor of the shadow-count zone
`SHW = [1]·1^k` (anchor at `shwBase`, `k` source units right of it), write the value entry
`encodeNatEntryR k = 0·1^(k+2)` at the value-stack frontier — **leaving the shadow count intact**.

Geometry (all walks are content walks; **no position arithmetic**):

* the value stack sits left of `SHW` across an all-`0` corridor and always ends in a `1`
  (`encodeNatStackR_getLast_true` — the base sentinel when empty), so a leftward `0`-scan from
  `shwBase − 1` always lands on the append anchor;
* a **pre-hop** writes the entry's first framing `1` two cells right of that anchor (the skipped
  cell is the entry's leading `0`), making every later append uniform ("land on the entry run's
  end, step right, write");
* each **fan-out pass** appends one `1` to the entry, erases the source's rightmost unit, and
  re-deposits it **two cells right of the erased cell** — a fixed hop, no search — so the rebuilt
  block grows leftward with a **constant gap of 2** from the shrinking source and ends, after `k`
  passes, exactly at `[shwBase+3, shwBase+k+3)`;
* the **relocate loop** then moves the rebuilt block back onto the source footprint one unit per
  pass (test two right of the dest frontier; erase there; write at the frontier), restoring
  `SHW = [1]·1^k` in place;
* the **epilogue** appends the entry's second framing `1` and parks the head on the home anchor at
  the sink.

Phase layout (`N = 81`):
`0–11` pre-hop (stepLeft · scanLeft₀ · stepRight ×2 · write[1] · scanRight₀ ↦ 12) ·
`12–15` HOME sink-test (`stepRightThenBranch`: src `1` ↦ 16, drained `0` ↦ 52) ·
`16–51` fan-out pass (stepLeft ×2 · scanLeft₀ · stepRight · write[1] · scanRight₀ · stepRight ·
scanRight₁ · stepLeft · write[0] · stepRight · write[1] · stepLeft ×4 · scanLeft₁ · stepRight ↦ 12) ·
`52–67` relocate (stepRight · branch (`1` ↦ 58, done `0` ↦ 68) · write[0] · stepLeft ×3 ·
write[1] ↦ 52) ·
`68–79` epilogue (scanLeft₀ · scanLeft₁ · scanLeft₀ · stepRight · write[1] · scanRight₀ ↦ 80) ·
`80` sink.

**Progress classification (AGENTS.md): Infrastructure** — a staging machine and its region
contracts; proves no separation.  Standard `[propext, Classical.choice, Quot.sound]` triple only.
**No `P ≠ NP` claim.** -/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-- The value-push phase assignment (see the layout table in the module docstring). -/
def valuePushAssign : Nat → RegionAction := fun i =>
  -- pre-hop: park the entry's first framing 1, return home
  if i < 2 then .run stepLeftOnce 0 (i - 0) (exitAt 1 2)
  else if i < 4 then .run selfLoopScanLeft 2 (i - 2) (exitAt 1 4)
  else if i < 6 then .run stepRightOnce 4 (i - 4) (exitAt 1 6)
  else if i < 8 then .run stepRightOnce 6 (i - 6) (exitAt 1 8)
  else if i < 10 then .run (writeBits [true]) 8 (i - 8) (exitAt 1 10)
  else if i < 12 then .run gammaSelfLoopScan 10 (i - 10) (exitAt 1 12)
  -- HOME: the sink test (source unit present ↦ pass, drained ↦ relocate)
  else if i < 16 then .run stepRightThenBranch 12 (i - 12)
    (fun j => if j = 2 then some 16 else if j = 3 then some 52 else none)
  -- fan-out pass: val append
  else if i < 18 then .run stepLeftOnce 16 (i - 16) (exitAt 1 18)
  else if i < 20 then .run stepLeftOnce 18 (i - 18) (exitAt 1 20)
  else if i < 22 then .run selfLoopScanLeft 20 (i - 20) (exitAt 1 22)
  else if i < 24 then .run stepRightOnce 22 (i - 22) (exitAt 1 24)
  else if i < 26 then .run (writeBits [true]) 24 (i - 24) (exitAt 1 26)
  else if i < 28 then .run gammaSelfLoopScan 26 (i - 26) (exitAt 1 28)
  -- fan-out pass: source erase + fixed re-deposit hop
  else if i < 30 then .run stepRightOnce 28 (i - 28) (exitAt 1 30)
  else if i < 32 then .run selfLoopScanRightOne 30 (i - 30) (exitAt 1 32)
  else if i < 34 then .run stepLeftOnce 32 (i - 32) (exitAt 1 34)
  else if i < 36 then .run (writeBits [false]) 34 (i - 34) (exitAt 1 36)
  else if i < 38 then .run stepRightOnce 36 (i - 36) (exitAt 1 38)
  else if i < 40 then .run (writeBits [true]) 38 (i - 38) (exitAt 1 40)
  -- fan-out pass: walk home (4 fixed lefts, the 1-run, step back onto the anchor)
  else if i < 42 then .run stepLeftOnce 40 (i - 40) (exitAt 1 42)
  else if i < 44 then .run stepLeftOnce 42 (i - 42) (exitAt 1 44)
  else if i < 46 then .run stepLeftOnce 44 (i - 44) (exitAt 1 46)
  else if i < 48 then .run stepLeftOnce 46 (i - 46) (exitAt 1 48)
  else if i < 50 then .run selfLoopScanLeftOne 48 (i - 48) (exitAt 1 50)
  else if i < 52 then .run stepRightOnce 50 (i - 50) (exitAt 1 12)
  -- relocate: test two right of the frontier, erase there, write at the frontier
  else if i < 54 then .run stepRightOnce 52 (i - 52) (exitAt 1 54)
  else if i < 58 then .run stepRightThenBranch 54 (i - 54)
    (fun j => if j = 2 then some 58 else if j = 3 then some 68 else none)
  else if i < 60 then .run (writeBits [false]) 58 (i - 58) (exitAt 1 60)
  else if i < 62 then .run stepLeftOnce 60 (i - 60) (exitAt 1 62)
  else if i < 64 then .run stepLeftOnce 62 (i - 62) (exitAt 1 64)
  else if i < 66 then .run stepLeftOnce 64 (i - 64) (exitAt 1 66)
  else if i < 68 then .run (writeBits [true]) 66 (i - 66) (exitAt 1 52)
  -- epilogue: second framing 1, park on the home anchor
  else if i < 70 then .run selfLoopScanLeft 68 (i - 68) (exitAt 1 70)
  else if i < 72 then .run selfLoopScanLeftOne 70 (i - 70) (exitAt 1 72)
  else if i < 74 then .run selfLoopScanLeft 72 (i - 72) (exitAt 1 74)
  else if i < 76 then .run stepRightOnce 74 (i - 74) (exitAt 1 76)
  else if i < 78 then .run (writeBits [true]) 76 (i - 76) (exitAt 1 78)
  else if i < 80 then .run gammaSelfLoopScan 78 (i - 78) (exitAt 1 80)
  -- sink
  else .idle

/-- **The value-push machine** (81 phases; start at the pre-hop `0`, nominal accept = the sink
`80`). -/
def valuePushProgram : ConstStatePhasedProgram Unit :=
  unionProgram 81 (by omega) ⟨0, by omega⟩ ⟨80, by omega⟩ valuePushAssign

@[simp] theorem valuePushProgram_numPhases : valuePushProgram.numPhases = 81 := rfl

@[simp] theorem valuePushProgram_startPhase : (valuePushProgram.startPhase : Nat) = 0 := rfl

/-! ### The region contracts (one instantiation each) -/

theorem valuePush_region_preStepLeft :
    RegionEmbedded valuePushProgram stepLeftOnce 0 2 := by
  refine RegionEmbeddedMulti.toSingle ?_
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [stepLeftOnce]) ?_
  · intro k hk
    have hk' : k < 2 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

theorem valuePush_region_preScanLeft :
    RegionEmbedded valuePushProgram selfLoopScanLeft 2 4 := by
  refine RegionEmbeddedMulti.toSingle ?_
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [selfLoopScanLeft]) ?_
  · intro k hk
    have hk' : k < 2 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

theorem valuePush_region_preStepRight1 :
    RegionEmbedded valuePushProgram stepRightOnce 4 6 := by
  refine RegionEmbeddedMulti.toSingle ?_
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [stepRightOnce]) ?_
  · intro k hk
    have hk' : k < 2 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

theorem valuePush_region_preStepRight2 :
    RegionEmbedded valuePushProgram stepRightOnce 6 8 := by
  refine RegionEmbeddedMulti.toSingle ?_
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [stepRightOnce]) ?_
  · intro k hk
    have hk' : k < 2 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

theorem valuePush_region_preWrite :
    RegionEmbedded valuePushProgram (writeBits [true]) 8 10 := by
  refine RegionEmbeddedMulti.toSingle ?_
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [writeBits]) ?_
  · intro k hk
    have hk' : k < 2 := by simpa [writeBits] using hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

theorem valuePush_region_preScanRight :
    RegionEmbedded valuePushProgram gammaSelfLoopScan 10 12 := by
  refine RegionEmbeddedMulti.toSingle ?_
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [gammaSelfLoopScan]) ?_
  · intro k hk
    have hk' : k < 2 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

theorem valuePush_region_homeBranch :
    RegionEmbeddedMulti valuePushProgram stepRightThenBranch 12
      (fun j => if j = 2 then some 16 else if j = 3 then some 52 else none) := by
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [stepRightThenBranch]) ?_
  · intro k hk
    have hk' : k < 4 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    split at h
    · cases h; omega
    · split at h
      · cases h; omega
      · cases h

theorem valuePush_region_passStepLeft1 :
    RegionEmbedded valuePushProgram stepLeftOnce 16 18 := by
  refine RegionEmbeddedMulti.toSingle ?_
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [stepLeftOnce]) ?_
  · intro k hk
    have hk' : k < 2 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

theorem valuePush_region_passStepLeft2 :
    RegionEmbedded valuePushProgram stepLeftOnce 18 20 := by
  refine RegionEmbeddedMulti.toSingle ?_
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [stepLeftOnce]) ?_
  · intro k hk
    have hk' : k < 2 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

theorem valuePush_region_passScanLeft :
    RegionEmbedded valuePushProgram selfLoopScanLeft 20 22 := by
  refine RegionEmbeddedMulti.toSingle ?_
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [selfLoopScanLeft]) ?_
  · intro k hk
    have hk' : k < 2 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

theorem valuePush_region_passStepRightVal :
    RegionEmbedded valuePushProgram stepRightOnce 22 24 := by
  refine RegionEmbeddedMulti.toSingle ?_
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [stepRightOnce]) ?_
  · intro k hk
    have hk' : k < 2 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

theorem valuePush_region_passWriteVal :
    RegionEmbedded valuePushProgram (writeBits [true]) 24 26 := by
  refine RegionEmbeddedMulti.toSingle ?_
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [writeBits]) ?_
  · intro k hk
    have hk' : k < 2 := by simpa [writeBits] using hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

theorem valuePush_region_passScanRightHome :
    RegionEmbedded valuePushProgram gammaSelfLoopScan 26 28 := by
  refine RegionEmbeddedMulti.toSingle ?_
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [gammaSelfLoopScan]) ?_
  · intro k hk
    have hk' : k < 2 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

theorem valuePush_region_passStepRightSrc :
    RegionEmbedded valuePushProgram stepRightOnce 28 30 := by
  refine RegionEmbeddedMulti.toSingle ?_
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [stepRightOnce]) ?_
  · intro k hk
    have hk' : k < 2 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

theorem valuePush_region_passScanRightOnes :
    RegionEmbedded valuePushProgram selfLoopScanRightOne 30 32 := by
  refine RegionEmbeddedMulti.toSingle ?_
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [selfLoopScanRightOne]) ?_
  · intro k hk
    have hk' : k < 2 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

theorem valuePush_region_passStepLeftErase :
    RegionEmbedded valuePushProgram stepLeftOnce 32 34 := by
  refine RegionEmbeddedMulti.toSingle ?_
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [stepLeftOnce]) ?_
  · intro k hk
    have hk' : k < 2 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

theorem valuePush_region_passErase :
    RegionEmbedded valuePushProgram (writeBits [false]) 34 36 := by
  refine RegionEmbeddedMulti.toSingle ?_
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [writeBits]) ?_
  · intro k hk
    have hk' : k < 2 := by simpa [writeBits] using hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

theorem valuePush_region_passStepRightDeposit :
    RegionEmbedded valuePushProgram stepRightOnce 36 38 := by
  refine RegionEmbeddedMulti.toSingle ?_
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [stepRightOnce]) ?_
  · intro k hk
    have hk' : k < 2 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

theorem valuePush_region_passDeposit :
    RegionEmbedded valuePushProgram (writeBits [true]) 38 40 := by
  refine RegionEmbeddedMulti.toSingle ?_
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [writeBits]) ?_
  · intro k hk
    have hk' : k < 2 := by simpa [writeBits] using hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

theorem valuePush_region_passHomeLeft1 :
    RegionEmbedded valuePushProgram stepLeftOnce 40 42 := by
  refine RegionEmbeddedMulti.toSingle ?_
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [stepLeftOnce]) ?_
  · intro k hk
    have hk' : k < 2 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

theorem valuePush_region_passHomeLeft2 :
    RegionEmbedded valuePushProgram stepLeftOnce 42 44 := by
  refine RegionEmbeddedMulti.toSingle ?_
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [stepLeftOnce]) ?_
  · intro k hk
    have hk' : k < 2 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

theorem valuePush_region_passHomeLeft3 :
    RegionEmbedded valuePushProgram stepLeftOnce 44 46 := by
  refine RegionEmbeddedMulti.toSingle ?_
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [stepLeftOnce]) ?_
  · intro k hk
    have hk' : k < 2 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

theorem valuePush_region_passHomeLeft4 :
    RegionEmbedded valuePushProgram stepLeftOnce 46 48 := by
  refine RegionEmbeddedMulti.toSingle ?_
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [stepLeftOnce]) ?_
  · intro k hk
    have hk' : k < 2 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

theorem valuePush_region_passHomeOnes :
    RegionEmbedded valuePushProgram selfLoopScanLeftOne 48 50 := by
  refine RegionEmbeddedMulti.toSingle ?_
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [selfLoopScanLeftOne]) ?_
  · intro k hk
    have hk' : k < 2 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

theorem valuePush_region_passHomeStepRight :
    RegionEmbedded valuePushProgram stepRightOnce 50 12 := by
  refine RegionEmbeddedMulti.toSingle ?_
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [stepRightOnce]) ?_
  · intro k hk
    have hk' : k < 2 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

theorem valuePush_region_relocStepRight :
    RegionEmbedded valuePushProgram stepRightOnce 52 54 := by
  refine RegionEmbeddedMulti.toSingle ?_
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [stepRightOnce]) ?_
  · intro k hk
    have hk' : k < 2 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

theorem valuePush_region_relocBranch :
    RegionEmbeddedMulti valuePushProgram stepRightThenBranch 54
      (fun j => if j = 2 then some 58 else if j = 3 then some 68 else none) := by
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [stepRightThenBranch]) ?_
  · intro k hk
    have hk' : k < 4 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    split at h
    · cases h; omega
    · split at h
      · cases h; omega
      · cases h

theorem valuePush_region_relocErase :
    RegionEmbedded valuePushProgram (writeBits [false]) 58 60 := by
  refine RegionEmbeddedMulti.toSingle ?_
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [writeBits]) ?_
  · intro k hk
    have hk' : k < 2 := by simpa [writeBits] using hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

theorem valuePush_region_relocLeft1 :
    RegionEmbedded valuePushProgram stepLeftOnce 60 62 := by
  refine RegionEmbeddedMulti.toSingle ?_
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [stepLeftOnce]) ?_
  · intro k hk
    have hk' : k < 2 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

theorem valuePush_region_relocLeft2 :
    RegionEmbedded valuePushProgram stepLeftOnce 62 64 := by
  refine RegionEmbeddedMulti.toSingle ?_
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [stepLeftOnce]) ?_
  · intro k hk
    have hk' : k < 2 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

theorem valuePush_region_relocLeft3 :
    RegionEmbedded valuePushProgram stepLeftOnce 64 66 := by
  refine RegionEmbeddedMulti.toSingle ?_
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [stepLeftOnce]) ?_
  · intro k hk
    have hk' : k < 2 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

theorem valuePush_region_relocWrite :
    RegionEmbedded valuePushProgram (writeBits [true]) 66 52 := by
  refine RegionEmbeddedMulti.toSingle ?_
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [writeBits]) ?_
  · intro k hk
    have hk' : k < 2 := by simpa [writeBits] using hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

theorem valuePush_region_epiScanLeft1 :
    RegionEmbedded valuePushProgram selfLoopScanLeft 68 70 := by
  refine RegionEmbeddedMulti.toSingle ?_
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [selfLoopScanLeft]) ?_
  · intro k hk
    have hk' : k < 2 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

theorem valuePush_region_epiScanOnes :
    RegionEmbedded valuePushProgram selfLoopScanLeftOne 70 72 := by
  refine RegionEmbeddedMulti.toSingle ?_
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [selfLoopScanLeftOne]) ?_
  · intro k hk
    have hk' : k < 2 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

theorem valuePush_region_epiScanLeft2 :
    RegionEmbedded valuePushProgram selfLoopScanLeft 72 74 := by
  refine RegionEmbeddedMulti.toSingle ?_
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [selfLoopScanLeft]) ?_
  · intro k hk
    have hk' : k < 2 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

theorem valuePush_region_epiStepRight :
    RegionEmbedded valuePushProgram stepRightOnce 74 76 := by
  refine RegionEmbeddedMulti.toSingle ?_
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [stepRightOnce]) ?_
  · intro k hk
    have hk' : k < 2 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

theorem valuePush_region_epiWrite :
    RegionEmbedded valuePushProgram (writeBits [true]) 76 78 := by
  refine RegionEmbeddedMulti.toSingle ?_
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [writeBits]) ?_
  · intro k hk
    have hk' : k < 2 := by simpa [writeBits] using hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

theorem valuePush_region_epiScanRight :
    RegionEmbedded valuePushProgram gammaSelfLoopScan 78 80 := by
  refine RegionEmbeddedMulti.toSingle ?_
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [gammaSelfLoopScan]) ?_
  · intro k hk
    have hk' : k < 2 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

/-- The sink phase `80` idles: phase, head, and tape are all preserved. -/
theorem valuePush_sink_idle {L : Nat}
    (c : Configuration (M := valuePushProgram.toPhased.toTM) L)
    (hphase : (c.state.fst : Nat) = 80) :
    (((TM.stepConfig (M := valuePushProgram.toPhased.toTM) c).state).fst : Nat) = 80
    ∧ (TM.stepConfig (M := valuePushProgram.toPhased.toTM) c).head = c.head
    ∧ (TM.stepConfig (M := valuePushProgram.toPhased.toTM) c).tape = c.tape := by
  have hstate : c.state = ⟨c.state.fst, c.state.snd⟩ := rfl
  have htr : valuePushProgram.transition c.state.fst c.state.snd (c.tape c.head)
      = (c.state.fst, (), c.tape c.head, Move.stay) := by
    show (unionProgram 81 (by omega) ⟨0, by omega⟩ ⟨80, by omega⟩ valuePushAssign).transition
      c.state.fst c.state.snd (c.tape c.head) = _
    have hass : valuePushAssign (c.state.fst : Nat) = RegionAction.idle := by
      rw [hphase]; rfl
    simp only [unionProgram, hass]
  refine ⟨?_, ?_, ?_⟩
  · rw [toTM_stepConfig_phase valuePushProgram c hstate, htr]
    exact hphase
  · rw [toTM_stepConfig_head valuePushProgram c hstate, htr]
    simp [Configuration.moveHead]
  · rw [toTM_stepConfig_tape valuePushProgram c hstate, htr]
    funext q
    by_cases hq : q = c.head
    · subst hq; simp [Configuration.write]
    · simp [Configuration.write, hq]

end ContractExpansion
end Frontier
end Pnp4
