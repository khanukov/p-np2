import Pnp4.Frontier.ContractExpansion.TreeMCSPNodeIterProgram
import Pnp4.Frontier.ContractExpansion.TreeMCSPRegionValuePushHop
import Pnp4.Frontier.ContractExpansion.TreeMCSPRegionBitProbeHop
import Pnp4.Frontier.ContractExpansion.TreeMCSPRegionScanOnesSegments

/-!
# `constIterProgram` — D2t-5b (Block A5m-6, machine): the const-leaf iteration as a region union

One full **const-leaf** iteration of the driver: from the read home at the cursor marker, step
onto the cursor, read the tag (`certTrie`, fft = const), probe the value bit `b` in place
(`bitProbe`), and per `b` (the record `[1,0,b]` differs): walk back over the consumed 4-bit
token, rewrite the marker block (`[0,0,0,0,1]` from the old marker — `constStepTape`'s cursor
part), travel the six leftward legs to the WORK frontier (cert dead → ctrl top, walk ctrl,
→ SHW top, cross SHW, → val top, walk val, → FM), write the record-plus-replant block
`[1,0,b,1]` at `FM` (`emitTape`'s record part — the chains converge here), and run the shared
tail: back right to the value frontier (`γ`-scan to the val sentinel, walk val rightward, one
step left onto `opBase`), the **whole A5m-V value-push region** (the entry `0·1^(k+2)` fan-out
from the `SHW` source, restored in place), then the return with the **`SHW` tick** (cross the
entry, `γ`-scan to `shwBase`, cross `SHW`, write the tick `1`, `γ`-scan to the ctrl sentinel,
walk ctrl rightward, `γ`-scan home onto the **new** marker).

Phase layout (`N = 170`): `0–1` stepRight · `2–13` certTrie (const ↦ 14, others ↦ 169) ·
`14–16` bitProbe (`0` ↦ 17, `1` ↦ 60) · per b: 4×stepLeft · marker `writeBits [0,0,0,0,1]` ·
2×stepLeft · scanLeft · zoneWalkLeft · scanLeft · scanLeftOne · scanLeft · zoneWalkLeft ·
scanLeft · record `writeBits [1,0,b,1]` (↦ 103) · shared: `103` γ-scan · `105` zoneWalkRight ·
`111` stepLeft · `113–147` valuePush (↦ 148) · `148` stepRight · `150` scanRightOne · `152`
γ-scan · `154` scanRightOne · `156` tick `writeBits [1]` · `158` γ-scan · `160` zoneWalkRight ·
`166` γ-scan (↦ 168) · `168` out · `169` stuck.

**Progress classification (AGENTS.md): Infrastructure** — a staging machine and its region
contracts; proves no separation.  Standard `[propext, Classical.choice, Quot.sound]` triple only.
**No `P ≠ NP` claim.** -/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram
open Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-- The const marker-rewrite block (`constStepTape`'s cursor part: the old marker and the four
token cells zeroed, the new marker planted on the token's last cell). -/
def constMarkBlock : List Bool := [false, false, false, false, true]

@[simp] theorem constMarkBlock_length : constMarkBlock.length = 5 := rfl

/-- The const record-plus-replant block: the record `[1,0,b]` merged with the new frontier
marker `1` (the record's leading `1` overwrites the old `FM`). -/
def constRecBlock (b : Bool) : List Bool := [true, false, b, true]

@[simp] theorem constRecBlock_length (b : Bool) : (constRecBlock b).length = 4 := rfl

/-- The certTrie redirect map of the const machine: the const verdict (`φ7`) enters the probe;
every other verdict routes to `stuck`. -/
def constTrieRedirect : Nat → Option Nat :=
  fun j => if j = 6 then some 169 else if j = 7 then some 14 else if j = 8 then some 169
    else if j = 9 then some 169 else if j = 10 then some 169 else if j = 11 then some 169
    else none

/-- The bit-probe redirect map: `b = 0` (slot `1`) enters the `b = 0` chain, `b = 1` (slot `2`)
the `b = 1` chain. -/
def constProbeRedirect : Nat → Option Nat :=
  fun j => if j = 1 then some 17 else if j = 2 then some 60 else none

/-- The const-iteration phase assignment (see the layout table in the module docstring). -/
def constIterAssign : Nat → RegionAction := fun i =>
  if i < 2 then .run stepRightOnce 0 (i - 0) (exitAt 1 2)
  else if i < 14 then .run certTrie 2 (i - 2) (constTrieRedirect)
  else if i < 17 then .run bitProbe 14 (i - 14) (constProbeRedirect)
  else if i < 19 then .run stepLeftOnce 17 (i - 17) (exitAt 1 19)
  else if i < 21 then .run stepLeftOnce 19 (i - 19) (exitAt 1 21)
  else if i < 23 then .run stepLeftOnce 21 (i - 21) (exitAt 1 23)
  else if i < 25 then .run stepLeftOnce 23 (i - 23) (exitAt 1 25)
  else if i < 31 then .run (writeBits constMarkBlock) 25 (i - 25) (exitAt 5 31)
  else if i < 33 then .run stepLeftOnce 31 (i - 31) (exitAt 1 33)
  else if i < 35 then .run stepLeftOnce 33 (i - 33) (exitAt 1 35)
  else if i < 37 then .run selfLoopScanLeft 35 (i - 35) (exitAt 1 37)
  else if i < 42 then .run zoneWalkLeft 37 (i - 37) (exitAt 4 42)
  else if i < 44 then .run selfLoopScanLeft 42 (i - 42) (exitAt 1 44)
  else if i < 46 then .run selfLoopScanLeftOne 44 (i - 44) (exitAt 1 46)
  else if i < 48 then .run selfLoopScanLeft 46 (i - 46) (exitAt 1 48)
  else if i < 53 then .run zoneWalkLeft 48 (i - 48) (exitAt 4 53)
  else if i < 55 then .run selfLoopScanLeft 53 (i - 53) (exitAt 1 55)
  else if i < 60 then .run (writeBits (constRecBlock false)) 55 (i - 55) (exitAt 4 103)
  else if i < 62 then .run stepLeftOnce 60 (i - 60) (exitAt 1 62)
  else if i < 64 then .run stepLeftOnce 62 (i - 62) (exitAt 1 64)
  else if i < 66 then .run stepLeftOnce 64 (i - 64) (exitAt 1 66)
  else if i < 68 then .run stepLeftOnce 66 (i - 66) (exitAt 1 68)
  else if i < 74 then .run (writeBits constMarkBlock) 68 (i - 68) (exitAt 5 74)
  else if i < 76 then .run stepLeftOnce 74 (i - 74) (exitAt 1 76)
  else if i < 78 then .run stepLeftOnce 76 (i - 76) (exitAt 1 78)
  else if i < 80 then .run selfLoopScanLeft 78 (i - 78) (exitAt 1 80)
  else if i < 85 then .run zoneWalkLeft 80 (i - 80) (exitAt 4 85)
  else if i < 87 then .run selfLoopScanLeft 85 (i - 85) (exitAt 1 87)
  else if i < 89 then .run selfLoopScanLeftOne 87 (i - 87) (exitAt 1 89)
  else if i < 91 then .run selfLoopScanLeft 89 (i - 89) (exitAt 1 91)
  else if i < 96 then .run zoneWalkLeft 91 (i - 91) (exitAt 4 96)
  else if i < 98 then .run selfLoopScanLeft 96 (i - 96) (exitAt 1 98)
  else if i < 103 then .run (writeBits (constRecBlock true)) 98 (i - 98) (exitAt 4 103)
  else if i < 105 then .run gammaSelfLoopScan 103 (i - 103) (exitAt 1 105)
  else if i < 111 then .run zoneWalkRight 105 (i - 105) (exitAt 4 111)
  else if i < 113 then .run stepLeftOnce 111 (i - 111) (exitAt 1 113)
  else if i < 148 then .run valuePushProgram 113 (i - 113) (exitAt 34 148)
  else if i < 150 then .run stepRightOnce 148 (i - 148) (exitAt 1 150)
  else if i < 152 then .run selfLoopScanRightOne 150 (i - 150) (exitAt 1 152)
  else if i < 154 then .run gammaSelfLoopScan 152 (i - 152) (exitAt 1 154)
  else if i < 156 then .run selfLoopScanRightOne 154 (i - 154) (exitAt 1 156)
  else if i < 158 then .run (writeBits [true]) 156 (i - 156) (exitAt 1 158)
  else if i < 160 then .run gammaSelfLoopScan 158 (i - 158) (exitAt 1 160)
  else if i < 166 then .run zoneWalkRight 160 (i - 160) (exitAt 4 166)
  else if i < 168 then .run gammaSelfLoopScan 166 (i - 166) (exitAt 1 168)
  else .idle

/-- **The const iteration machine** (170 phases; start at the read home `0`, nominal accept at
the home-read out `168`). -/
def constIterProgram : ConstStatePhasedProgram Unit :=
  unionProgram 170 (by omega) ⟨0, by omega⟩ ⟨168, by omega⟩ constIterAssign

/-! ### The region contracts -/

theorem constIter_region_sR_0 :
    RegionEmbedded constIterProgram stepRightOnce 0 2 := by
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

theorem constIter_region_trie_2 :
    RegionEmbeddedMulti constIterProgram certTrie 2 constTrieRedirect := by
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [certTrie]) ?_
  · intro k hk
    have hk' : k < 12 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold constTrieRedirect at h
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
            · split at h
              · cases h; omega
              · cases h

theorem constIter_region_probe_14 :
    RegionEmbeddedMulti constIterProgram bitProbe 14 constProbeRedirect := by
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [bitProbe]) ?_
  · intro k hk
    have hk' : k < 3 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold constProbeRedirect at h
    split at h
    · cases h; omega
    · split at h
      · cases h; omega
      · cases h

theorem constIter_region_sL_17 :
    RegionEmbedded constIterProgram stepLeftOnce 17 19 := by
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

theorem constIter_region_sL2_19 :
    RegionEmbedded constIterProgram stepLeftOnce 19 21 := by
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

theorem constIter_region_sL3_21 :
    RegionEmbedded constIterProgram stepLeftOnce 21 23 := by
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

theorem constIter_region_sL4_23 :
    RegionEmbedded constIterProgram stepLeftOnce 23 25 := by
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

theorem constIter_region_mark_25 :
    RegionEmbedded constIterProgram (writeBits constMarkBlock) 25 31 := by
  have hacc : ((writeBits constMarkBlock).acceptPhase : Nat) = 5 := by
    simp [writeBits]
  refine RegionEmbeddedMulti.toSingle ?_
  rw [show (fun j => if j = (((writeBits constMarkBlock)).acceptPhase : Nat)
      then some 31 else none) = exitAt 5 31 from by
    funext j; rw [hacc]; rfl]
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_
    (by simp only [unionProgram_numPhases, writeBits_numPhases, constMarkBlock_length]
        omega) ?_
  · intro k hk
    have hk' : k < 6 := by
      have := hk
      simp only [writeBits_numPhases, constMarkBlock_length] at this
      omega
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

theorem constIter_region_sL5_31 :
    RegionEmbedded constIterProgram stepLeftOnce 31 33 := by
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

theorem constIter_region_sL6_33 :
    RegionEmbedded constIterProgram stepLeftOnce 33 35 := by
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

theorem constIter_region_scanL_35 :
    RegionEmbedded constIterProgram selfLoopScanLeft 35 37 := by
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

theorem constIter_region_walkL_37 :
    RegionEmbeddedMulti constIterProgram zoneWalkLeft 37 (exitAt 4 42) := by
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [zoneWalkLeft]) ?_
  · intro k hk
    have hk' : k < 5 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

theorem constIter_region_scanL2_42 :
    RegionEmbedded constIterProgram selfLoopScanLeft 42 44 := by
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

theorem constIter_region_scanL1_44 :
    RegionEmbedded constIterProgram selfLoopScanLeftOne 44 46 := by
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

theorem constIter_region_scanL3_46 :
    RegionEmbedded constIterProgram selfLoopScanLeft 46 48 := by
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

theorem constIter_region_walkL2_48 :
    RegionEmbeddedMulti constIterProgram zoneWalkLeft 48 (exitAt 4 53) := by
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [zoneWalkLeft]) ?_
  · intro k hk
    have hk' : k < 5 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

theorem constIter_region_scanL4_53 :
    RegionEmbedded constIterProgram selfLoopScanLeft 53 55 := by
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

theorem constIter_region_rec0_55 :
    RegionEmbedded constIterProgram (writeBits (constRecBlock false)) 55 103 := by
  have hacc : ((writeBits (constRecBlock false)).acceptPhase : Nat) = 4 := by
    simp [writeBits]
  refine RegionEmbeddedMulti.toSingle ?_
  rw [show (fun j => if j = (((writeBits (constRecBlock false))).acceptPhase : Nat)
      then some 103 else none) = exitAt 4 103 from by
    funext j; rw [hacc]; rfl]
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_
    (by simp only [unionProgram_numPhases, writeBits_numPhases, constRecBlock_length]
        omega) ?_
  · intro k hk
    have hk' : k < 5 := by
      have := hk
      simp only [writeBits_numPhases, constRecBlock_length] at this
      omega
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

theorem constIter_region_sL7_60 :
    RegionEmbedded constIterProgram stepLeftOnce 60 62 := by
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

theorem constIter_region_sL8_62 :
    RegionEmbedded constIterProgram stepLeftOnce 62 64 := by
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

theorem constIter_region_sL9_64 :
    RegionEmbedded constIterProgram stepLeftOnce 64 66 := by
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

theorem constIter_region_sL10_66 :
    RegionEmbedded constIterProgram stepLeftOnce 66 68 := by
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

theorem constIter_region_mark2_68 :
    RegionEmbedded constIterProgram (writeBits constMarkBlock) 68 74 := by
  have hacc : ((writeBits constMarkBlock).acceptPhase : Nat) = 5 := by
    simp [writeBits]
  refine RegionEmbeddedMulti.toSingle ?_
  rw [show (fun j => if j = (((writeBits constMarkBlock)).acceptPhase : Nat)
      then some 74 else none) = exitAt 5 74 from by
    funext j; rw [hacc]; rfl]
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_
    (by simp only [unionProgram_numPhases, writeBits_numPhases, constMarkBlock_length]
        omega) ?_
  · intro k hk
    have hk' : k < 6 := by
      have := hk
      simp only [writeBits_numPhases, constMarkBlock_length] at this
      omega
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

theorem constIter_region_sL11_74 :
    RegionEmbedded constIterProgram stepLeftOnce 74 76 := by
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

theorem constIter_region_sL12_76 :
    RegionEmbedded constIterProgram stepLeftOnce 76 78 := by
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

theorem constIter_region_scanL5_78 :
    RegionEmbedded constIterProgram selfLoopScanLeft 78 80 := by
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

theorem constIter_region_walkL3_80 :
    RegionEmbeddedMulti constIterProgram zoneWalkLeft 80 (exitAt 4 85) := by
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [zoneWalkLeft]) ?_
  · intro k hk
    have hk' : k < 5 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

theorem constIter_region_scanL6_85 :
    RegionEmbedded constIterProgram selfLoopScanLeft 85 87 := by
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

theorem constIter_region_scanL12_87 :
    RegionEmbedded constIterProgram selfLoopScanLeftOne 87 89 := by
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

theorem constIter_region_scanL7_89 :
    RegionEmbedded constIterProgram selfLoopScanLeft 89 91 := by
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

theorem constIter_region_walkL4_91 :
    RegionEmbeddedMulti constIterProgram zoneWalkLeft 91 (exitAt 4 96) := by
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [zoneWalkLeft]) ?_
  · intro k hk
    have hk' : k < 5 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

theorem constIter_region_scanL8_96 :
    RegionEmbedded constIterProgram selfLoopScanLeft 96 98 := by
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

theorem constIter_region_rec1_98 :
    RegionEmbedded constIterProgram (writeBits (constRecBlock true)) 98 103 := by
  have hacc : ((writeBits (constRecBlock true)).acceptPhase : Nat) = 4 := by
    simp [writeBits]
  refine RegionEmbeddedMulti.toSingle ?_
  rw [show (fun j => if j = (((writeBits (constRecBlock true))).acceptPhase : Nat)
      then some 103 else none) = exitAt 4 103 from by
    funext j; rw [hacc]; rfl]
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_
    (by simp only [unionProgram_numPhases, writeBits_numPhases, constRecBlock_length]
        omega) ?_
  · intro k hk
    have hk' : k < 5 := by
      have := hk
      simp only [writeBits_numPhases, constRecBlock_length] at this
      omega
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

theorem constIter_region_scanR_103 :
    RegionEmbedded constIterProgram gammaSelfLoopScan 103 105 := by
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

theorem constIter_region_walkR_105 :
    RegionEmbeddedMulti constIterProgram zoneWalkRight 105 (exitAt 4 111) := by
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [zoneWalkRight]) ?_
  · intro k hk
    have hk' : k < 6 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

theorem constIter_region_sL13_111 :
    RegionEmbedded constIterProgram stepLeftOnce 111 113 := by
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

theorem constIter_region_vpush_113 :
    RegionEmbeddedMulti constIterProgram valuePushProgram 113 (exitAt 34 148) := by
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [valuePushProgram]) ?_
  · intro k hk
    have hk' : k < 35 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

theorem constIter_region_sR2_148 :
    RegionEmbedded constIterProgram stepRightOnce 148 150 := by
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

theorem constIter_region_scanR1_150 :
    RegionEmbedded constIterProgram selfLoopScanRightOne 150 152 := by
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

theorem constIter_region_scanR2_152 :
    RegionEmbedded constIterProgram gammaSelfLoopScan 152 154 := by
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

theorem constIter_region_scanR12_154 :
    RegionEmbedded constIterProgram selfLoopScanRightOne 154 156 := by
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

theorem constIter_region_tick_156 :
    RegionEmbedded constIterProgram (writeBits [true]) 156 158 := by
  have hacc : ((writeBits [true]).acceptPhase : Nat) = 1 := by
    simp [writeBits]
  refine RegionEmbeddedMulti.toSingle ?_
  rw [show (fun j => if j = (((writeBits [true])).acceptPhase : Nat)
      then some 158 else none) = exitAt 1 158 from by
    funext j; rw [hacc]; rfl]
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_
    (by simp only [unionProgram_numPhases, writeBits_numPhases, List.length_singleton]
        omega) ?_
  · intro k hk
    have hk' : k < 2 := by
      have := hk
      simp only [writeBits_numPhases, List.length_singleton] at this
      omega
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

theorem constIter_region_scanR3_158 :
    RegionEmbedded constIterProgram gammaSelfLoopScan 158 160 := by
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

theorem constIter_region_walkR2_160 :
    RegionEmbeddedMulti constIterProgram zoneWalkRight 160 (exitAt 4 166) := by
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [zoneWalkRight]) ?_
  · intro k hk
    have hk' : k < 6 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

theorem constIter_region_scanR4_166 :
    RegionEmbedded constIterProgram gammaSelfLoopScan 166 168 := by
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

end ContractExpansion
end Frontier
end Pnp4
