import Pnp4.Frontier.ContractExpansion.TreeMCSPRegionUnion

/-!
# `clearIterProgram` — D2t-5b (Block A5m-3, machine): the settle-clear iteration as a region union

The first concrete machine on the U1–U5 stack: one full **clear** iteration of the driver — from
the settle home at the cursor marker, step left, scan to the control top, probe (the **empty**
verdict), step back over the sentinel, scan home — built as a `unionProgram` assignment over the
merged components, with every region contract obtained by one `unionProgram_embedded`
instantiation.  The frame verdict routes to a designated `stuck` phase: this staging machine
handles exactly the clear branch (the full driver adds the dec/pop arms at that exit).

Phase layout (`N = 16`):

| base | component | redirects |
|---|---|---|
| 0–1 | `stepLeftOnce` | accept `1` ↦ `2` |
| 2–3 | `selfLoopScanLeft` | accept `1` ↦ `4` |
| 4–7 | `settleProbe` | empty `3` ↦ `8`, frame `2` ↦ `15` (stuck) |
| 8–9 | `stepRightOnce` | accept `1` ↦ `10` |
| 10–11 | `stepRightOnce` | accept `1` ↦ `12` |
| 12–13 | `gammaSelfLoopScan` | accept `1` ↦ `14` |
| 14 | home-read out (idle) | — |
| 15 | stuck (idle) | — |

Also provides `RegionEmbeddedMulti.toSingle`: a one-point redirect map (exactly the accept phase)
downgrades to the `RegionEmbedded` contract, unlocking the U3 generic hops for builder regions.

**Progress classification (AGENTS.md): Infrastructure** — a staging machine and its region
contracts; proves no separation.  Standard `[propext, Classical.choice, Quot.sound]` triple only.
**No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-- A one-point redirect map (exactly the component's accept phase) downgrades the multi-exit
contract to the single-exit one, unlocking the U3 generic hops. -/
theorem RegionEmbeddedMulti.toSingle {U P : ConstStatePhasedProgram Unit} {base next : Nat}
    (h : RegionEmbeddedMulti U P base
      (fun j => if j = (P.acceptPhase : Nat) then some next else none)) :
    RegionEmbedded U P base next := by
  refine ⟨h.fit, h.redirect_lt (j := (P.acceptPhase : Nat)) (nxt := next) (by simp),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j b hj
    exact h.normal_phase j b (by simp [hj])
  · intro j b hj
    exact h.normal_bit j b (by simp [hj])
  · intro j b hj
    exact h.normal_move j b (by simp [hj])
  · intro b
    exact h.redirect_phase P.acceptPhase b (nxt := next) (by simp)
  · intro b
    exact h.redirect_bit P.acceptPhase b (nxt := next) (by simp)
  · intro b
    exact h.redirect_move P.acceptPhase b (nxt := next) (by simp)

/-- The clear-iteration phase assignment (see the layout table in the module docstring). -/
def clearIterAssign : Nat → RegionAction
  | 0 => .run stepLeftOnce 0 0 (fun j => if j = 1 then some 2 else none)
  | 1 => .run stepLeftOnce 0 1 (fun j => if j = 1 then some 2 else none)
  | 2 => .run selfLoopScanLeft 2 0 (fun j => if j = 1 then some 4 else none)
  | 3 => .run selfLoopScanLeft 2 1 (fun j => if j = 1 then some 4 else none)
  | 4 => .run settleProbe 4 0 (fun j => if j = 3 then some 8 else if j = 2 then some 15 else none)
  | 5 => .run settleProbe 4 1 (fun j => if j = 3 then some 8 else if j = 2 then some 15 else none)
  | 6 => .run settleProbe 4 2 (fun j => if j = 3 then some 8 else if j = 2 then some 15 else none)
  | 7 => .run settleProbe 4 3 (fun j => if j = 3 then some 8 else if j = 2 then some 15 else none)
  | 8 => .run stepRightOnce 8 0 (fun j => if j = 1 then some 10 else none)
  | 9 => .run stepRightOnce 8 1 (fun j => if j = 1 then some 10 else none)
  | 10 => .run stepRightOnce 10 0 (fun j => if j = 1 then some 12 else none)
  | 11 => .run stepRightOnce 10 1 (fun j => if j = 1 then some 12 else none)
  | 12 => .run gammaSelfLoopScan 12 0 (fun j => if j = 1 then some 14 else none)
  | 13 => .run gammaSelfLoopScan 12 1 (fun j => if j = 1 then some 14 else none)
  | _ => .idle

/-- **The settle-clear iteration machine** (16 phases; start at the settle home `0`, nominal accept
at the home-read out `14`). -/
def clearIterProgram : ConstStatePhasedProgram Unit :=
  unionProgram 16 (by omega) ⟨0, by omega⟩ ⟨14, by omega⟩ clearIterAssign

/-! ### The region contracts (one instantiation each) -/

/-- Region `0–1`: the opening left step. -/
theorem clearIter_region_stepLeft :
    RegionEmbedded clearIterProgram stepLeftOnce 0 2 := by
  refine RegionEmbeddedMulti.toSingle ?_
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [stepLeftOnce]) ?_
  · intro k hk
    have hk' : k < 2 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    split at h
    · cases h; omega
    · cases h

/-- Region `2–3`: the leftward corridor scan onto the control top. -/
theorem clearIter_region_scanLeft :
    RegionEmbedded clearIterProgram selfLoopScanLeft 2 4 := by
  refine RegionEmbeddedMulti.toSingle ?_
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [selfLoopScanLeft]) ?_
  · intro k hk
    have hk' : k < 2 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    split at h
    · cases h; omega
    · cases h

/-- Region `4–7`: the probe (empty ↦ `8`, frame ↦ `15`). -/
theorem clearIter_region_probe :
    RegionEmbeddedMulti clearIterProgram settleProbe 4
      (fun j => if j = 3 then some 8 else if j = 2 then some 15 else none) := by
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [settleProbe]) ?_
  · intro k hk
    have hk' : k < 4 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    split at h
    · cases h; omega
    · split at h
      · cases h; omega
      · cases h

/-- Region `8–9`: the first right step (off the dead cell onto the sentinel). -/
theorem clearIter_region_stepRight1 :
    RegionEmbedded clearIterProgram stepRightOnce 8 10 := by
  refine RegionEmbeddedMulti.toSingle ?_
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [stepRightOnce]) ?_
  · intro k hk
    have hk' : k < 2 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    split at h
    · cases h; omega
    · cases h

/-- Region `10–11`: the second right step (over the sentinel into the dead corridor). -/
theorem clearIter_region_stepRight2 :
    RegionEmbedded clearIterProgram stepRightOnce 10 12 := by
  refine RegionEmbeddedMulti.toSingle ?_
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [stepRightOnce]) ?_
  · intro k hk
    have hk' : k < 2 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    split at h
    · cases h; omega
    · cases h

/-- Region `12–13`: the rightward corridor scan home onto the cursor marker. -/
theorem clearIter_region_scanRight :
    RegionEmbedded clearIterProgram gammaSelfLoopScan 12 14 := by
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
