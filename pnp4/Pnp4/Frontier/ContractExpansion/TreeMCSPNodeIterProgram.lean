import Pnp4.Frontier.ContractExpansion.TreeMCSPCertTrie

/-!
# `nodeIterProgram` — D2t-5b (Block A5m-5, machine): the node iteration as a region union

One full **node** iteration of the driver: from the read home at the cursor marker, step onto the
cursor, read the tag (`certTrie`), walk back, rewrite the marker block (`[0,0,0,1]` from the old
marker cell — `nodeStepTape`'s cursor part), hop to the control top, push the `(tag, arity)` frame
(`writeBits` at the first free cell — `nodeStepTape`'s frame part), and scan home onto the **new**
marker.  Per-tag chains after the trie verdicts; leaf/reject verdicts route to `stuck` (this
staging machine handles exactly the node branch).

Phase layout (`N = 116`): `0–1` stepRight · `2–13` certTrie (not ↦ 14, and ↦ 46, or ↦ 80, others ↦
115) · per tag: 4×stepLeft · marker `writeBits [0,0,0,1]` · 2×stepLeft · scanLeft · stepRight ·
frame `writeBits (encodeCtrlFrameR (tag, arity))` (↦ 112) · `112–113` scanRight (↦ 114) · `114`
out · `115` stuck.

**Progress classification (AGENTS.md): Infrastructure** — a staging machine and its region
contracts; proves no separation.  Standard `[propext, Classical.choice, Quot.sound]` triple only.
**No `P ≠ NP` claim.** -/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram
open Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-- The node marker-rewrite block (`nodeStepTape`'s cursor part, written from the old marker). -/
def nodeMarkBlock : List Bool := [false, false, false, true]

@[simp] theorem nodeMarkBlock_length : nodeMarkBlock.length = 4 := rfl

/-- The node frame blocks: the pushed `(tag, arity)` frame. -/
def nodeFrame (tag : ITag) : List Bool := encodeCtrlFrameR (tag, tag.arity)

@[simp] theorem nodeFrame_length (tag : ITag) :
    (nodeFrame tag).length = tag.arity + tag.tagCode + 5 := by
  simp [nodeFrame, encodeCtrlFrameR_length]

/-- The certTrie redirect map of the node machine. -/
def nodeTrieRedirect : Nat → Option Nat :=
  fun j => if j = 6 then some 115 else if j = 7 then some 115 else if j = 8 then some 14
    else if j = 9 then some 46 else if j = 10 then some 80 else if j = 11 then some 115
    else none

/-- A single-exit redirect map. -/
def exitAt (a nxt : Nat) : Nat → Option Nat := fun j => if j = a then some nxt else none

/-- The node-iteration phase assignment (see the layout table in the module docstring). -/
def nodeIterAssign : Nat → RegionAction := fun i =>
  if i < 2 then .run stepRightOnce 0 (i - 0) (exitAt 1 2)
  else if i < 14 then .run certTrie 2 (i - 2) nodeTrieRedirect
  -- the NOT chain
  else if i < 16 then .run stepLeftOnce 14 (i - 14) (exitAt 1 16)
  else if i < 18 then .run stepLeftOnce 16 (i - 16) (exitAt 1 18)
  else if i < 20 then .run stepLeftOnce 18 (i - 18) (exitAt 1 20)
  else if i < 22 then .run stepLeftOnce 20 (i - 20) (exitAt 1 22)
  else if i < 27 then .run (writeBits nodeMarkBlock) 22 (i - 22) (exitAt 4 27)
  else if i < 29 then .run stepLeftOnce 27 (i - 27) (exitAt 1 29)
  else if i < 31 then .run stepLeftOnce 29 (i - 29) (exitAt 1 31)
  else if i < 33 then .run selfLoopScanLeft 31 (i - 31) (exitAt 1 33)
  else if i < 35 then .run stepRightOnce 33 (i - 33) (exitAt 1 35)
  else if i < 42 then .run (writeBits (nodeFrame ITag.tnot)) 35 (i - 35) (exitAt 6 112)
  -- the AND chain
  else if i < 48 then if i < 46 then .idle else .run stepLeftOnce 46 (i - 46) (exitAt 1 48)
  else if i < 50 then .run stepLeftOnce 48 (i - 48) (exitAt 1 50)
  else if i < 52 then .run stepLeftOnce 50 (i - 50) (exitAt 1 52)
  else if i < 54 then .run stepLeftOnce 52 (i - 52) (exitAt 1 54)
  else if i < 59 then .run (writeBits nodeMarkBlock) 54 (i - 54) (exitAt 4 59)
  else if i < 61 then .run stepLeftOnce 59 (i - 59) (exitAt 1 61)
  else if i < 63 then .run stepLeftOnce 61 (i - 61) (exitAt 1 63)
  else if i < 65 then .run selfLoopScanLeft 63 (i - 63) (exitAt 1 65)
  else if i < 67 then .run stepRightOnce 65 (i - 65) (exitAt 1 67)
  else if i < 76 then .run (writeBits (nodeFrame ITag.tand)) 67 (i - 67) (exitAt 8 112)
  -- the OR chain
  else if i < 82 then if i < 80 then .idle else .run stepLeftOnce 80 (i - 80) (exitAt 1 82)
  else if i < 84 then .run stepLeftOnce 82 (i - 82) (exitAt 1 84)
  else if i < 86 then .run stepLeftOnce 84 (i - 84) (exitAt 1 86)
  else if i < 88 then .run stepLeftOnce 86 (i - 86) (exitAt 1 88)
  else if i < 93 then .run (writeBits nodeMarkBlock) 88 (i - 88) (exitAt 4 93)
  else if i < 95 then .run stepLeftOnce 93 (i - 93) (exitAt 1 95)
  else if i < 97 then .run stepLeftOnce 95 (i - 95) (exitAt 1 97)
  else if i < 99 then .run selfLoopScanLeft 97 (i - 97) (exitAt 1 99)
  else if i < 101 then .run stepRightOnce 99 (i - 99) (exitAt 1 101)
  else if i < 111 then .run (writeBits (nodeFrame ITag.tor)) 101 (i - 101) (exitAt 9 112)
  -- the shared return
  else if i = 111 then .idle
  else if i < 114 then .run gammaSelfLoopScan 112 (i - 112) (exitAt 1 114)
  else .idle

/-- **The node iteration machine** (116 phases; start at the read home `0`, nominal accept at the
home-read out `114`). -/
def nodeIterProgram : ConstStatePhasedProgram Unit :=
  unionProgram 116 (by omega) ⟨0, by omega⟩ ⟨114, by omega⟩ nodeIterAssign

/-! ### The region contracts -/

theorem nodeIter_region_stepRight :
    RegionEmbedded nodeIterProgram stepRightOnce 0 2 := by
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

theorem nodeIter_region_certTrie :
    RegionEmbeddedMulti nodeIterProgram certTrie 2 nodeTrieRedirect := by
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [certTrie]) ?_
  · intro k hk
    have hk' : k < 12 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold nodeTrieRedirect at h
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

theorem nodeIter_region_Not_sL1 :
    RegionEmbedded nodeIterProgram stepLeftOnce 14 16 := by
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

theorem nodeIter_region_Not_sL2 :
    RegionEmbedded nodeIterProgram stepLeftOnce 16 18 := by
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

theorem nodeIter_region_Not_sL3 :
    RegionEmbedded nodeIterProgram stepLeftOnce 18 20 := by
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

theorem nodeIter_region_Not_sL4 :
    RegionEmbedded nodeIterProgram stepLeftOnce 20 22 := by
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

theorem nodeIter_region_Not_mark :
    RegionEmbedded nodeIterProgram (writeBits nodeMarkBlock) 22 27 := by
  have hacc : ((writeBits nodeMarkBlock).acceptPhase : Nat) = 4 := by
    simp [writeBits, nodeMarkBlock]
  refine RegionEmbeddedMulti.toSingle ?_
  rw [show (fun j => if j = (((writeBits nodeMarkBlock)).acceptPhase : Nat)
      then some 27 else none) = exitAt 4 27 from by
    funext j; rw [hacc]; rfl]
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_
    (by simp only [unionProgram_numPhases, writeBits_numPhases, nodeMarkBlock_length,
          nodeFrame_length, ITag.arity, ITag.tagCode]
        omega) ?_
  · intro k hk
    have hk' : k < 5 := by
      have := hk
      simp only [writeBits_numPhases, nodeMarkBlock_length, nodeFrame_length,
        ITag.arity, ITag.tagCode] at this
      omega
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

theorem nodeIter_region_Not_sL5 :
    RegionEmbedded nodeIterProgram stepLeftOnce 27 29 := by
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

theorem nodeIter_region_Not_sL6 :
    RegionEmbedded nodeIterProgram stepLeftOnce 29 31 := by
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

theorem nodeIter_region_Not_scanL :
    RegionEmbedded nodeIterProgram selfLoopScanLeft 31 33 := by
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

theorem nodeIter_region_Not_sR :
    RegionEmbedded nodeIterProgram stepRightOnce 33 35 := by
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

theorem nodeIter_region_Not_frame :
    RegionEmbedded nodeIterProgram (writeBits (nodeFrame ITag.tnot)) 35 112 := by
  have hacc : ((writeBits (nodeFrame ITag.tnot)).acceptPhase : Nat) = 6 := by
    simp [writeBits, nodeFrame_length, ITag.arity, ITag.tagCode]
  refine RegionEmbeddedMulti.toSingle ?_
  rw [show (fun j => if j = (((writeBits (nodeFrame ITag.tnot))).acceptPhase : Nat)
      then some 112 else none) = exitAt 6 112 from by
    funext j; rw [hacc]; rfl]
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_
    (by simp only [unionProgram_numPhases, writeBits_numPhases, nodeMarkBlock_length,
          nodeFrame_length, ITag.arity, ITag.tagCode]
        omega) ?_
  · intro k hk
    have hk' : k < 7 := by
      have := hk
      simp only [writeBits_numPhases, nodeMarkBlock_length, nodeFrame_length,
        ITag.arity, ITag.tagCode] at this
      omega
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

theorem nodeIter_region_And_sL1 :
    RegionEmbedded nodeIterProgram stepLeftOnce 46 48 := by
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

theorem nodeIter_region_And_sL2 :
    RegionEmbedded nodeIterProgram stepLeftOnce 48 50 := by
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

theorem nodeIter_region_And_sL3 :
    RegionEmbedded nodeIterProgram stepLeftOnce 50 52 := by
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

theorem nodeIter_region_And_sL4 :
    RegionEmbedded nodeIterProgram stepLeftOnce 52 54 := by
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

theorem nodeIter_region_And_mark :
    RegionEmbedded nodeIterProgram (writeBits nodeMarkBlock) 54 59 := by
  have hacc : ((writeBits nodeMarkBlock).acceptPhase : Nat) = 4 := by
    simp [writeBits, nodeMarkBlock]
  refine RegionEmbeddedMulti.toSingle ?_
  rw [show (fun j => if j = (((writeBits nodeMarkBlock)).acceptPhase : Nat)
      then some 59 else none) = exitAt 4 59 from by
    funext j; rw [hacc]; rfl]
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_
    (by simp only [unionProgram_numPhases, writeBits_numPhases, nodeMarkBlock_length,
          nodeFrame_length, ITag.arity, ITag.tagCode]
        omega) ?_
  · intro k hk
    have hk' : k < 5 := by
      have := hk
      simp only [writeBits_numPhases, nodeMarkBlock_length, nodeFrame_length,
        ITag.arity, ITag.tagCode] at this
      omega
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

theorem nodeIter_region_And_sL5 :
    RegionEmbedded nodeIterProgram stepLeftOnce 59 61 := by
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

theorem nodeIter_region_And_sL6 :
    RegionEmbedded nodeIterProgram stepLeftOnce 61 63 := by
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

theorem nodeIter_region_And_scanL :
    RegionEmbedded nodeIterProgram selfLoopScanLeft 63 65 := by
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

theorem nodeIter_region_And_sR :
    RegionEmbedded nodeIterProgram stepRightOnce 65 67 := by
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

theorem nodeIter_region_And_frame :
    RegionEmbedded nodeIterProgram (writeBits (nodeFrame ITag.tand)) 67 112 := by
  have hacc : ((writeBits (nodeFrame ITag.tand)).acceptPhase : Nat) = 8 := by
    simp [writeBits, nodeFrame_length, ITag.arity, ITag.tagCode]
  refine RegionEmbeddedMulti.toSingle ?_
  rw [show (fun j => if j = (((writeBits (nodeFrame ITag.tand))).acceptPhase : Nat)
      then some 112 else none) = exitAt 8 112 from by
    funext j; rw [hacc]; rfl]
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_
    (by simp only [unionProgram_numPhases, writeBits_numPhases, nodeMarkBlock_length,
          nodeFrame_length, ITag.arity, ITag.tagCode]
        omega) ?_
  · intro k hk
    have hk' : k < 9 := by
      have := hk
      simp only [writeBits_numPhases, nodeMarkBlock_length, nodeFrame_length,
        ITag.arity, ITag.tagCode] at this
      omega
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

theorem nodeIter_region_Or_sL1 :
    RegionEmbedded nodeIterProgram stepLeftOnce 80 82 := by
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

theorem nodeIter_region_Or_sL2 :
    RegionEmbedded nodeIterProgram stepLeftOnce 82 84 := by
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

theorem nodeIter_region_Or_sL3 :
    RegionEmbedded nodeIterProgram stepLeftOnce 84 86 := by
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

theorem nodeIter_region_Or_sL4 :
    RegionEmbedded nodeIterProgram stepLeftOnce 86 88 := by
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

theorem nodeIter_region_Or_mark :
    RegionEmbedded nodeIterProgram (writeBits nodeMarkBlock) 88 93 := by
  have hacc : ((writeBits nodeMarkBlock).acceptPhase : Nat) = 4 := by
    simp [writeBits, nodeMarkBlock]
  refine RegionEmbeddedMulti.toSingle ?_
  rw [show (fun j => if j = (((writeBits nodeMarkBlock)).acceptPhase : Nat)
      then some 93 else none) = exitAt 4 93 from by
    funext j; rw [hacc]; rfl]
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_
    (by simp only [unionProgram_numPhases, writeBits_numPhases, nodeMarkBlock_length,
          nodeFrame_length, ITag.arity, ITag.tagCode]
        omega) ?_
  · intro k hk
    have hk' : k < 5 := by
      have := hk
      simp only [writeBits_numPhases, nodeMarkBlock_length, nodeFrame_length,
        ITag.arity, ITag.tagCode] at this
      omega
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

theorem nodeIter_region_Or_sL5 :
    RegionEmbedded nodeIterProgram stepLeftOnce 93 95 := by
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

theorem nodeIter_region_Or_sL6 :
    RegionEmbedded nodeIterProgram stepLeftOnce 95 97 := by
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

theorem nodeIter_region_Or_scanL :
    RegionEmbedded nodeIterProgram selfLoopScanLeft 97 99 := by
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

theorem nodeIter_region_Or_sR :
    RegionEmbedded nodeIterProgram stepRightOnce 99 101 := by
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

theorem nodeIter_region_Or_frame :
    RegionEmbedded nodeIterProgram (writeBits (nodeFrame ITag.tor)) 101 112 := by
  have hacc : ((writeBits (nodeFrame ITag.tor)).acceptPhase : Nat) = 9 := by
    simp [writeBits, nodeFrame_length, ITag.arity, ITag.tagCode]
  refine RegionEmbeddedMulti.toSingle ?_
  rw [show (fun j => if j = (((writeBits (nodeFrame ITag.tor))).acceptPhase : Nat)
      then some 112 else none) = exitAt 9 112 from by
    funext j; rw [hacc]; rfl]
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_
    (by simp only [unionProgram_numPhases, writeBits_numPhases, nodeMarkBlock_length,
          nodeFrame_length, ITag.arity, ITag.tagCode]
        omega) ?_
  · intro k hk
    have hk' : k < 10 := by
      have := hk
      simp only [writeBits_numPhases, nodeMarkBlock_length, nodeFrame_length,
        ITag.arity, ITag.tagCode] at this
      omega
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

theorem nodeIter_region_scanRight :
    RegionEmbedded nodeIterProgram gammaSelfLoopScan 112 114 := by
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
