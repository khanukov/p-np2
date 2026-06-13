import Pnp4.Frontier.ContractExpansion.TreeMCSPDecIterProgram
import Pnp4.Frontier.ContractExpansion.TreeMCSPConstIterProgram
import Pnp4.Frontier.ContractExpansion.TreeMCSPRegionUnaryTransferHop

/-!
# `popIterProgram` — D2t-5b (Block A5m-8, machine): the settle-pop-emit iteration as a region union

One full **pop** iteration of the driver (settling, top frame `(tag, 1)`): from the settle home at
the cursor marker, step off and 0-scan to the control top, read the tag (`ctrlTopWalk`) and the
rem block (`remWalk`, the `rem = 1` pop verdict — landing on the frame's base), and per tag:
erase the whole frame (`writeBits 0^flen` — `popStepTape`'s control part), descend the six legs to
`FM`, write the record's unary tag block `1^tagCode·0` (the old `FM` consumed by the first `1`),
re-ascend to the value top, and run the shared **field pipelines**: per popped operand, the
shuttle loop drains the top value entry one `1` at a time into a parking block just left of the
value sentinel (the cell `valBase − 1` stays `0`, preserving the walkers' dead-cell anchors; the
stop is a `bitProbe` double-left peek — the entry's leading `0` flags the last two framing ones,
which the cleanup zeroes), then one `unaryTransfer` region moves the parked block across the
all-zero gap into the record's operand field (`opBase` = two right of the record's last `1`, so
the same navigation serves every field).  `tnot` runs one pipeline, `tand`/`tor` two.  The shared
finish replants `FM`, runs the **A5m-V value-push region** at the new value frontier, writes the
`SHW` tick, and 0-scans home onto the (unmoved) cursor marker.

Phase layout (`N = 428`): `0–37` entry (stepLeft · 0-scan · `ctrlTopWalk` (tags ↦ the three
`remWalk`s) · 3×`remWalk` (`rem = 1` ↦ the tag track, else ↦ stuck)) · tracks `38`/`83`/`131`
(frame erase · descent · tag write · ascent) · `181` PIPE1 · `261` re-ascent · `273` PIPE2 ·
`353` finish (FM · value push `371–405` · tick · rehome) · `426` out · `427` stuck.

**Progress classification (AGENTS.md): Infrastructure** — a staging machine and its region
contracts; proves no separation.  Standard `[propext, Classical.choice, Quot.sound]` triple only.
**No `P ≠ NP` claim.** -/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram
open Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-- The ctrlTopWalk redirect map of the pop machine: tags enter their `remWalk`s. -/
def popCtrlTopRedirect : Nat → Option Nat :=
  fun j => if j = 5 then some 427 else if j = 6 then some 14 else if j = 7 then some 22
    else if j = 8 then some 30 else if j = 9 then some 427 else none

/-- The per-tag remWalk redirect maps (`rem = 1` ↦ the tag track, dec/reject ↦ stuck). -/
def popRemRedirect (tbase : Nat) : Nat → Option Nat :=
  fun j => if j = 5 then some tbase else if j = 6 then some 427 else if j = 7 then some 427
    else none

set_option maxRecDepth 8192 in
/-- The pop-iteration phase assignment (see the layout table in the module docstring). -/
def popIterAssign : Nat → RegionAction := fun i =>
  if i < 2 then .run stepLeftOnce 0 (i - 0) (exitAt 1 2)
  else if i < 4 then .run selfLoopScanLeft 2 (i - 2) (exitAt 1 4)
  else if i < 14 then .run ctrlTopWalk 4 (i - 4) popCtrlTopRedirect
  else if i < 22 then .run remWalk 14 (i - 14) (popRemRedirect 38)
  else if i < 30 then .run remWalk 22 (i - 22) (popRemRedirect 83)
  else if i < 38 then .run remWalk 30 (i - 30) (popRemRedirect 131)
  else if i < 47 then .run (writeBits (List.replicate 8 false)) 38 (i - 38) (exitAt 8 47)
  else if i < 49 then .run selfLoopScanLeft 47 (i - 47) (exitAt 1 49)
  else if i < 54 then .run zoneWalkLeft 49 (i - 49) (exitAt 4 54)
  else if i < 56 then .run selfLoopScanLeft 54 (i - 54) (exitAt 1 56)
  else if i < 58 then .run selfLoopScanLeftOne 56 (i - 56) (exitAt 1 58)
  else if i < 60 then .run selfLoopScanLeft 58 (i - 58) (exitAt 1 60)
  else if i < 65 then .run zoneWalkLeft 60 (i - 60) (exitAt 4 65)
  else if i < 67 then .run selfLoopScanLeft 65 (i - 65) (exitAt 1 67)
  else if i < 71 then .run (writeBits (List.replicate 2 true ++ [false])) 67 (i - 67) (exitAt 3 71)
  else if i < 73 then .run gammaSelfLoopScan 71 (i - 71) (exitAt 1 73)
  else if i < 79 then .run zoneWalkRight 73 (i - 73) (exitAt 4 79)
  else if i < 81 then .run stepLeftOnce 79 (i - 79) (exitAt 1 81)
  else if i < 83 then .run stepLeftOnce 81 (i - 81) (exitAt 1 273)
  else if i < 94 then .run (writeBits (List.replicate 10 false)) 83 (i - 83) (exitAt 10 94)
  else if i < 96 then .run selfLoopScanLeft 94 (i - 94) (exitAt 1 96)
  else if i < 101 then .run zoneWalkLeft 96 (i - 96) (exitAt 4 101)
  else if i < 103 then .run selfLoopScanLeft 101 (i - 101) (exitAt 1 103)
  else if i < 105 then .run selfLoopScanLeftOne 103 (i - 103) (exitAt 1 105)
  else if i < 107 then .run selfLoopScanLeft 105 (i - 105) (exitAt 1 107)
  else if i < 112 then .run zoneWalkLeft 107 (i - 107) (exitAt 4 112)
  else if i < 114 then .run selfLoopScanLeft 112 (i - 112) (exitAt 1 114)
  else if i < 119 then .run (writeBits (List.replicate 3 true ++ [false])) 114 (i - 114) (exitAt 4 119)
  else if i < 121 then .run gammaSelfLoopScan 119 (i - 119) (exitAt 1 121)
  else if i < 127 then .run zoneWalkRight 121 (i - 121) (exitAt 4 127)
  else if i < 129 then .run stepLeftOnce 127 (i - 127) (exitAt 1 129)
  else if i < 131 then .run stepLeftOnce 129 (i - 129) (exitAt 1 181)
  else if i < 143 then .run (writeBits (List.replicate 11 false)) 131 (i - 131) (exitAt 11 143)
  else if i < 145 then .run selfLoopScanLeft 143 (i - 143) (exitAt 1 145)
  else if i < 150 then .run zoneWalkLeft 145 (i - 145) (exitAt 4 150)
  else if i < 152 then .run selfLoopScanLeft 150 (i - 150) (exitAt 1 152)
  else if i < 154 then .run selfLoopScanLeftOne 152 (i - 152) (exitAt 1 154)
  else if i < 156 then .run selfLoopScanLeft 154 (i - 154) (exitAt 1 156)
  else if i < 161 then .run zoneWalkLeft 156 (i - 156) (exitAt 4 161)
  else if i < 163 then .run selfLoopScanLeft 161 (i - 161) (exitAt 1 163)
  else if i < 169 then .run (writeBits (List.replicate 4 true ++ [false])) 163 (i - 163) (exitAt 5 169)
  else if i < 171 then .run gammaSelfLoopScan 169 (i - 169) (exitAt 1 171)
  else if i < 177 then .run zoneWalkRight 171 (i - 171) (exitAt 4 177)
  else if i < 179 then .run stepLeftOnce 177 (i - 177) (exitAt 1 179)
  else if i < 181 then .run stepLeftOnce 179 (i - 179) (exitAt 1 181)
  else if i < 183 then .run stepLeftOnce 181 (i - 181) (exitAt 1 183)
  else if i < 185 then .run stepLeftOnce 183 (i - 183) (exitAt 1 185)
  else if i < 188 then .run bitProbe 185 (i - 185) (fun j => if j = 1 then some 223 else if j = 2 then some 188 else none)
  else if i < 190 then .run stepRightOnce 188 (i - 188) (exitAt 1 190)
  else if i < 192 then .run stepRightOnce 190 (i - 190) (exitAt 1 192)
  else if i < 194 then .run (writeBits [false]) 192 (i - 192) (exitAt 1 194)
  else if i < 196 then .run stepLeftOnce 194 (i - 194) (exitAt 1 196)
  else if i < 198 then .run stepLeftOnce 196 (i - 196) (exitAt 1 198)
  else if i < 203 then .run zoneWalkLeft 198 (i - 198) (exitAt 4 203)
  else if i < 205 then .run stepLeftOnce 203 (i - 203) (exitAt 1 205)
  else if i < 207 then .run selfLoopScanLeftOne 205 (i - 205) (exitAt 1 207)
  else if i < 209 then .run (writeBits [true]) 207 (i - 207) (exitAt 1 209)
  else if i < 211 then .run selfLoopScanRightOne 209 (i - 209) (exitAt 1 211)
  else if i < 213 then .run stepRightOnce 211 (i - 211) (exitAt 1 213)
  else if i < 219 then .run zoneWalkRight 213 (i - 213) (exitAt 4 219)
  else if i < 221 then .run stepLeftOnce 219 (i - 219) (exitAt 1 221)
  else if i < 223 then .run stepLeftOnce 221 (i - 221) (exitAt 1 181)
  else if i < 225 then .run stepRightOnce 223 (i - 223) (exitAt 1 225)
  else if i < 227 then .run stepRightOnce 225 (i - 225) (exitAt 1 227)
  else if i < 229 then .run (writeBits [false]) 227 (i - 227) (exitAt 1 229)
  else if i < 231 then .run stepLeftOnce 229 (i - 229) (exitAt 1 231)
  else if i < 233 then .run stepLeftOnce 231 (i - 231) (exitAt 1 233)
  else if i < 235 then .run (writeBits [false]) 233 (i - 233) (exitAt 1 235)
  else if i < 237 then .run selfLoopScanLeft 235 (i - 235) (exitAt 1 237)
  else if i < 242 then .run zoneWalkLeft 237 (i - 237) (exitAt 4 242)
  else if i < 244 then .run stepLeftOnce 242 (i - 242) (exitAt 1 244)
  else if i < 246 then .run selfLoopScanLeftOne 244 (i - 244) (exitAt 1 246)
  else if i < 248 then .run selfLoopScanLeft 246 (i - 246) (exitAt 1 248)
  else if i < 250 then .run stepRightOnce 248 (i - 248) (exitAt 1 250)
  else if i < 252 then .run stepRightOnce 250 (i - 250) (exitAt 1 252)
  else if i < 261 then .run unaryTransfer 252 (i - 252) (exitAt 8 261)
  else if i < 263 then .run stepRightOnce 261 (i - 261) (exitAt 1 263)
  else if i < 269 then .run zoneWalkRight 263 (i - 263) (exitAt 4 269)
  else if i < 271 then .run stepLeftOnce 269 (i - 269) (exitAt 1 271)
  else if i < 273 then .run stepLeftOnce 271 (i - 271) (exitAt 1 273)
  else if i < 275 then .run stepLeftOnce 273 (i - 273) (exitAt 1 275)
  else if i < 277 then .run stepLeftOnce 275 (i - 275) (exitAt 1 277)
  else if i < 280 then .run bitProbe 277 (i - 277) (fun j => if j = 1 then some 315 else if j = 2 then some 280 else none)
  else if i < 282 then .run stepRightOnce 280 (i - 280) (exitAt 1 282)
  else if i < 284 then .run stepRightOnce 282 (i - 282) (exitAt 1 284)
  else if i < 286 then .run (writeBits [false]) 284 (i - 284) (exitAt 1 286)
  else if i < 288 then .run stepLeftOnce 286 (i - 286) (exitAt 1 288)
  else if i < 290 then .run stepLeftOnce 288 (i - 288) (exitAt 1 290)
  else if i < 295 then .run zoneWalkLeft 290 (i - 290) (exitAt 4 295)
  else if i < 297 then .run stepLeftOnce 295 (i - 295) (exitAt 1 297)
  else if i < 299 then .run selfLoopScanLeftOne 297 (i - 297) (exitAt 1 299)
  else if i < 301 then .run (writeBits [true]) 299 (i - 299) (exitAt 1 301)
  else if i < 303 then .run selfLoopScanRightOne 301 (i - 301) (exitAt 1 303)
  else if i < 305 then .run stepRightOnce 303 (i - 303) (exitAt 1 305)
  else if i < 311 then .run zoneWalkRight 305 (i - 305) (exitAt 4 311)
  else if i < 313 then .run stepLeftOnce 311 (i - 311) (exitAt 1 313)
  else if i < 315 then .run stepLeftOnce 313 (i - 313) (exitAt 1 273)
  else if i < 317 then .run stepRightOnce 315 (i - 315) (exitAt 1 317)
  else if i < 319 then .run stepRightOnce 317 (i - 317) (exitAt 1 319)
  else if i < 321 then .run (writeBits [false]) 319 (i - 319) (exitAt 1 321)
  else if i < 323 then .run stepLeftOnce 321 (i - 321) (exitAt 1 323)
  else if i < 325 then .run stepLeftOnce 323 (i - 323) (exitAt 1 325)
  else if i < 327 then .run (writeBits [false]) 325 (i - 325) (exitAt 1 327)
  else if i < 329 then .run selfLoopScanLeft 327 (i - 327) (exitAt 1 329)
  else if i < 334 then .run zoneWalkLeft 329 (i - 329) (exitAt 4 334)
  else if i < 336 then .run stepLeftOnce 334 (i - 334) (exitAt 1 336)
  else if i < 338 then .run selfLoopScanLeftOne 336 (i - 336) (exitAt 1 338)
  else if i < 340 then .run selfLoopScanLeft 338 (i - 338) (exitAt 1 340)
  else if i < 342 then .run stepRightOnce 340 (i - 340) (exitAt 1 342)
  else if i < 344 then .run stepRightOnce 342 (i - 342) (exitAt 1 344)
  else if i < 353 then .run unaryTransfer 344 (i - 344) (exitAt 8 353)
  else if i < 355 then .run selfLoopScanLeft 353 (i - 353) (exitAt 1 355)
  else if i < 357 then .run stepRightOnce 355 (i - 355) (exitAt 1 357)
  else if i < 359 then .run stepRightOnce 357 (i - 357) (exitAt 1 359)
  else if i < 361 then .run (writeBits [true]) 359 (i - 359) (exitAt 1 361)
  else if i < 363 then .run gammaSelfLoopScan 361 (i - 361) (exitAt 1 363)
  else if i < 369 then .run zoneWalkRight 363 (i - 363) (exitAt 4 369)
  else if i < 371 then .run stepLeftOnce 369 (i - 369) (exitAt 1 371)
  else if i < 406 then .run valuePushProgram 371 (i - 371) (exitAt 34 406)
  else if i < 408 then .run stepRightOnce 406 (i - 406) (exitAt 1 408)
  else if i < 410 then .run selfLoopScanRightOne 408 (i - 408) (exitAt 1 410)
  else if i < 412 then .run gammaSelfLoopScan 410 (i - 410) (exitAt 1 412)
  else if i < 414 then .run selfLoopScanRightOne 412 (i - 412) (exitAt 1 414)
  else if i < 416 then .run (writeBits [true]) 414 (i - 414) (exitAt 1 416)
  else if i < 418 then .run gammaSelfLoopScan 416 (i - 416) (exitAt 1 418)
  else if i < 424 then .run zoneWalkRight 418 (i - 418) (exitAt 4 424)
  else if i < 426 then .run gammaSelfLoopScan 424 (i - 424) (exitAt 1 426)
  else .idle

set_option maxRecDepth 8192 in
/-- **The pop iteration machine** (428 phases; start at the settle home `0`, nominal accept at
the home out `426`). -/
def popIterProgram : ConstStatePhasedProgram Unit :=
  unionProgram 428 (by omega) ⟨0, by omega⟩ ⟨426, by omega⟩ popIterAssign

/-! ### The region contracts -/

set_option maxRecDepth 8192 in
theorem popIter_region_sL_0 :
    RegionEmbedded popIterProgram stepLeftOnce 0 2 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_scanL_2 :
    RegionEmbedded popIterProgram selfLoopScanLeft 2 4 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_ctop_4 :
    RegionEmbeddedMulti popIterProgram ctrlTopWalk 4 (popCtrlTopRedirect) := by
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [ctrlTopWalk]) ?_
  · intro k hk
    have hk' : k < 10 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold popCtrlTopRedirect at h
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

set_option maxRecDepth 8192 in
theorem popIter_region_rem_14 :
    RegionEmbeddedMulti popIterProgram remWalk 14 (popRemRedirect 38) := by
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [remWalk]) ?_
  · intro k hk
    have hk' : k < 8 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold popRemRedirect at h
    split at h
    · cases h; omega
    · split at h
      · cases h; omega
      · split at h
        · cases h; omega
        · cases h

set_option maxRecDepth 8192 in
theorem popIter_region_rem_22 :
    RegionEmbeddedMulti popIterProgram remWalk 22 (popRemRedirect 83) := by
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [remWalk]) ?_
  · intro k hk
    have hk' : k < 8 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold popRemRedirect at h
    split at h
    · cases h; omega
    · split at h
      · cases h; omega
      · split at h
        · cases h; omega
        · cases h

set_option maxRecDepth 8192 in
theorem popIter_region_rem_30 :
    RegionEmbeddedMulti popIterProgram remWalk 30 (popRemRedirect 131) := by
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [remWalk]) ?_
  · intro k hk
    have hk' : k < 8 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold popRemRedirect at h
    split at h
    · cases h; omega
    · split at h
      · cases h; omega
      · split at h
        · cases h; omega
        · cases h

set_option maxRecDepth 8192 in
theorem popIter_region_wb_38 :
    RegionEmbedded popIterProgram (writeBits (List.replicate 8 false)) 38 47 := by
  have hacc : ((writeBits (List.replicate 8 false)).acceptPhase : Nat) = 8 := by
    simp [writeBits]
  refine RegionEmbeddedMulti.toSingle ?_
  rw [show (fun j => if j = (((writeBits (List.replicate 8 false))).acceptPhase : Nat)
      then some 47 else none) = exitAt 8 47 from by
    funext j; rw [hacc]; rfl]
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_
    (by simp only [unionProgram_numPhases, writeBits_numPhases, List.length_replicate,
          List.length_append, List.length_singleton]
        omega) ?_
  · intro k hk
    have hk' : k < 9 := by
      have := hk
      simp only [writeBits_numPhases, List.length_replicate, List.length_append,
        List.length_singleton] at this
      omega
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

set_option maxRecDepth 8192 in
theorem popIter_region_scanL_47 :
    RegionEmbedded popIterProgram selfLoopScanLeft 47 49 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_walkL_49 :
    RegionEmbeddedMulti popIterProgram zoneWalkLeft 49 (exitAt 4 54) := by
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [zoneWalkLeft]) ?_
  · intro k hk
    have hk' : k < 5 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

set_option maxRecDepth 8192 in
theorem popIter_region_scanL_54 :
    RegionEmbedded popIterProgram selfLoopScanLeft 54 56 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_scanL1_56 :
    RegionEmbedded popIterProgram selfLoopScanLeftOne 56 58 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_scanL_58 :
    RegionEmbedded popIterProgram selfLoopScanLeft 58 60 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_walkL_60 :
    RegionEmbeddedMulti popIterProgram zoneWalkLeft 60 (exitAt 4 65) := by
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [zoneWalkLeft]) ?_
  · intro k hk
    have hk' : k < 5 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

set_option maxRecDepth 8192 in
theorem popIter_region_scanL_65 :
    RegionEmbedded popIterProgram selfLoopScanLeft 65 67 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_wb_67 :
    RegionEmbedded popIterProgram (writeBits (List.replicate 2 true ++ [false])) 67 71 := by
  have hacc : ((writeBits (List.replicate 2 true ++ [false])).acceptPhase : Nat) = 3 := by
    simp [writeBits]
  refine RegionEmbeddedMulti.toSingle ?_
  rw [show (fun j => if j = (((writeBits (List.replicate 2 true ++ [false]))).acceptPhase : Nat)
      then some 71 else none) = exitAt 3 71 from by
    funext j; rw [hacc]; rfl]
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_
    (by simp only [unionProgram_numPhases, writeBits_numPhases, List.length_replicate,
          List.length_append, List.length_singleton]
        omega) ?_
  · intro k hk
    have hk' : k < 4 := by
      have := hk
      simp only [writeBits_numPhases, List.length_replicate, List.length_append,
        List.length_singleton] at this
      omega
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

set_option maxRecDepth 8192 in
theorem popIter_region_scanR_71 :
    RegionEmbedded popIterProgram gammaSelfLoopScan 71 73 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_walkR_73 :
    RegionEmbeddedMulti popIterProgram zoneWalkRight 73 (exitAt 4 79) := by
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [zoneWalkRight]) ?_
  · intro k hk
    have hk' : k < 6 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

set_option maxRecDepth 8192 in
theorem popIter_region_sL_79 :
    RegionEmbedded popIterProgram stepLeftOnce 79 81 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_sL_81 :
    RegionEmbedded popIterProgram stepLeftOnce 81 273 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_wb_83 :
    RegionEmbedded popIterProgram (writeBits (List.replicate 10 false)) 83 94 := by
  have hacc : ((writeBits (List.replicate 10 false)).acceptPhase : Nat) = 10 := by
    simp [writeBits]
  refine RegionEmbeddedMulti.toSingle ?_
  rw [show (fun j => if j = (((writeBits (List.replicate 10 false))).acceptPhase : Nat)
      then some 94 else none) = exitAt 10 94 from by
    funext j; rw [hacc]; rfl]
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_
    (by simp only [unionProgram_numPhases, writeBits_numPhases, List.length_replicate,
          List.length_append, List.length_singleton]
        omega) ?_
  · intro k hk
    have hk' : k < 11 := by
      have := hk
      simp only [writeBits_numPhases, List.length_replicate, List.length_append,
        List.length_singleton] at this
      omega
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

set_option maxRecDepth 8192 in
theorem popIter_region_scanL_94 :
    RegionEmbedded popIterProgram selfLoopScanLeft 94 96 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_walkL_96 :
    RegionEmbeddedMulti popIterProgram zoneWalkLeft 96 (exitAt 4 101) := by
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [zoneWalkLeft]) ?_
  · intro k hk
    have hk' : k < 5 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

set_option maxRecDepth 8192 in
theorem popIter_region_scanL_101 :
    RegionEmbedded popIterProgram selfLoopScanLeft 101 103 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_scanL1_103 :
    RegionEmbedded popIterProgram selfLoopScanLeftOne 103 105 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_scanL_105 :
    RegionEmbedded popIterProgram selfLoopScanLeft 105 107 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_walkL_107 :
    RegionEmbeddedMulti popIterProgram zoneWalkLeft 107 (exitAt 4 112) := by
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [zoneWalkLeft]) ?_
  · intro k hk
    have hk' : k < 5 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

set_option maxRecDepth 8192 in
theorem popIter_region_scanL_112 :
    RegionEmbedded popIterProgram selfLoopScanLeft 112 114 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_wb_114 :
    RegionEmbedded popIterProgram (writeBits (List.replicate 3 true ++ [false])) 114 119 := by
  have hacc : ((writeBits (List.replicate 3 true ++ [false])).acceptPhase : Nat) = 4 := by
    simp [writeBits]
  refine RegionEmbeddedMulti.toSingle ?_
  rw [show (fun j => if j = (((writeBits (List.replicate 3 true ++ [false]))).acceptPhase : Nat)
      then some 119 else none) = exitAt 4 119 from by
    funext j; rw [hacc]; rfl]
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_
    (by simp only [unionProgram_numPhases, writeBits_numPhases, List.length_replicate,
          List.length_append, List.length_singleton]
        omega) ?_
  · intro k hk
    have hk' : k < 5 := by
      have := hk
      simp only [writeBits_numPhases, List.length_replicate, List.length_append,
        List.length_singleton] at this
      omega
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

set_option maxRecDepth 8192 in
theorem popIter_region_scanR_119 :
    RegionEmbedded popIterProgram gammaSelfLoopScan 119 121 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_walkR_121 :
    RegionEmbeddedMulti popIterProgram zoneWalkRight 121 (exitAt 4 127) := by
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [zoneWalkRight]) ?_
  · intro k hk
    have hk' : k < 6 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

set_option maxRecDepth 8192 in
theorem popIter_region_sL_127 :
    RegionEmbedded popIterProgram stepLeftOnce 127 129 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_sL_129 :
    RegionEmbedded popIterProgram stepLeftOnce 129 181 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_wb_131 :
    RegionEmbedded popIterProgram (writeBits (List.replicate 11 false)) 131 143 := by
  have hacc : ((writeBits (List.replicate 11 false)).acceptPhase : Nat) = 11 := by
    simp [writeBits]
  refine RegionEmbeddedMulti.toSingle ?_
  rw [show (fun j => if j = (((writeBits (List.replicate 11 false))).acceptPhase : Nat)
      then some 143 else none) = exitAt 11 143 from by
    funext j; rw [hacc]; rfl]
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_
    (by simp only [unionProgram_numPhases, writeBits_numPhases, List.length_replicate,
          List.length_append, List.length_singleton]
        omega) ?_
  · intro k hk
    have hk' : k < 12 := by
      have := hk
      simp only [writeBits_numPhases, List.length_replicate, List.length_append,
        List.length_singleton] at this
      omega
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

set_option maxRecDepth 8192 in
theorem popIter_region_scanL_143 :
    RegionEmbedded popIterProgram selfLoopScanLeft 143 145 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_walkL_145 :
    RegionEmbeddedMulti popIterProgram zoneWalkLeft 145 (exitAt 4 150) := by
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [zoneWalkLeft]) ?_
  · intro k hk
    have hk' : k < 5 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

set_option maxRecDepth 8192 in
theorem popIter_region_scanL_150 :
    RegionEmbedded popIterProgram selfLoopScanLeft 150 152 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_scanL1_152 :
    RegionEmbedded popIterProgram selfLoopScanLeftOne 152 154 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_scanL_154 :
    RegionEmbedded popIterProgram selfLoopScanLeft 154 156 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_walkL_156 :
    RegionEmbeddedMulti popIterProgram zoneWalkLeft 156 (exitAt 4 161) := by
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [zoneWalkLeft]) ?_
  · intro k hk
    have hk' : k < 5 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

set_option maxRecDepth 8192 in
theorem popIter_region_scanL_161 :
    RegionEmbedded popIterProgram selfLoopScanLeft 161 163 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_wb_163 :
    RegionEmbedded popIterProgram (writeBits (List.replicate 4 true ++ [false])) 163 169 := by
  have hacc : ((writeBits (List.replicate 4 true ++ [false])).acceptPhase : Nat) = 5 := by
    simp [writeBits]
  refine RegionEmbeddedMulti.toSingle ?_
  rw [show (fun j => if j = (((writeBits (List.replicate 4 true ++ [false]))).acceptPhase : Nat)
      then some 169 else none) = exitAt 5 169 from by
    funext j; rw [hacc]; rfl]
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_
    (by simp only [unionProgram_numPhases, writeBits_numPhases, List.length_replicate,
          List.length_append, List.length_singleton]
        omega) ?_
  · intro k hk
    have hk' : k < 6 := by
      have := hk
      simp only [writeBits_numPhases, List.length_replicate, List.length_append,
        List.length_singleton] at this
      omega
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

set_option maxRecDepth 8192 in
theorem popIter_region_scanR_169 :
    RegionEmbedded popIterProgram gammaSelfLoopScan 169 171 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_walkR_171 :
    RegionEmbeddedMulti popIterProgram zoneWalkRight 171 (exitAt 4 177) := by
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [zoneWalkRight]) ?_
  · intro k hk
    have hk' : k < 6 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

set_option maxRecDepth 8192 in
theorem popIter_region_sL_177 :
    RegionEmbedded popIterProgram stepLeftOnce 177 179 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_sL_179 :
    RegionEmbedded popIterProgram stepLeftOnce 179 181 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_sL_181 :
    RegionEmbedded popIterProgram stepLeftOnce 181 183 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_sL_183 :
    RegionEmbedded popIterProgram stepLeftOnce 183 185 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_probe_185 :
    RegionEmbeddedMulti popIterProgram bitProbe 185
      (fun j => if j = 1 then some 223 else if j = 2 then some 188 else none) := by
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [bitProbe]) ?_
  · intro k hk
    have hk' : k < 3 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    split at h
    · cases h; omega
    · split at h
      · cases h; omega
      · cases h

set_option maxRecDepth 8192 in
theorem popIter_region_sR_188 :
    RegionEmbedded popIterProgram stepRightOnce 188 190 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_sR_190 :
    RegionEmbedded popIterProgram stepRightOnce 190 192 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_wb_192 :
    RegionEmbedded popIterProgram (writeBits [false]) 192 194 := by
  have hacc : ((writeBits [false]).acceptPhase : Nat) = 1 := by
    simp [writeBits]
  refine RegionEmbeddedMulti.toSingle ?_
  rw [show (fun j => if j = (((writeBits [false])).acceptPhase : Nat)
      then some 194 else none) = exitAt 1 194 from by
    funext j; rw [hacc]; rfl]
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_
    (by simp only [unionProgram_numPhases, writeBits_numPhases, List.length_replicate,
          List.length_append, List.length_singleton]
        omega) ?_
  · intro k hk
    have hk' : k < 2 := by
      have := hk
      simp only [writeBits_numPhases, List.length_replicate, List.length_append,
        List.length_singleton] at this
      omega
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

set_option maxRecDepth 8192 in
theorem popIter_region_sL_194 :
    RegionEmbedded popIterProgram stepLeftOnce 194 196 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_sL_196 :
    RegionEmbedded popIterProgram stepLeftOnce 196 198 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_walkL_198 :
    RegionEmbeddedMulti popIterProgram zoneWalkLeft 198 (exitAt 4 203) := by
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [zoneWalkLeft]) ?_
  · intro k hk
    have hk' : k < 5 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

set_option maxRecDepth 8192 in
theorem popIter_region_sL_203 :
    RegionEmbedded popIterProgram stepLeftOnce 203 205 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_scanL1_205 :
    RegionEmbedded popIterProgram selfLoopScanLeftOne 205 207 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_wb_207 :
    RegionEmbedded popIterProgram (writeBits [true]) 207 209 := by
  have hacc : ((writeBits [true]).acceptPhase : Nat) = 1 := by
    simp [writeBits]
  refine RegionEmbeddedMulti.toSingle ?_
  rw [show (fun j => if j = (((writeBits [true])).acceptPhase : Nat)
      then some 209 else none) = exitAt 1 209 from by
    funext j; rw [hacc]; rfl]
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_
    (by simp only [unionProgram_numPhases, writeBits_numPhases, List.length_replicate,
          List.length_append, List.length_singleton]
        omega) ?_
  · intro k hk
    have hk' : k < 2 := by
      have := hk
      simp only [writeBits_numPhases, List.length_replicate, List.length_append,
        List.length_singleton] at this
      omega
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

set_option maxRecDepth 8192 in
theorem popIter_region_scanR1_209 :
    RegionEmbedded popIterProgram selfLoopScanRightOne 209 211 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_sR_211 :
    RegionEmbedded popIterProgram stepRightOnce 211 213 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_walkR_213 :
    RegionEmbeddedMulti popIterProgram zoneWalkRight 213 (exitAt 4 219) := by
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [zoneWalkRight]) ?_
  · intro k hk
    have hk' : k < 6 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

set_option maxRecDepth 8192 in
theorem popIter_region_sL_219 :
    RegionEmbedded popIterProgram stepLeftOnce 219 221 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_sL_221 :
    RegionEmbedded popIterProgram stepLeftOnce 221 181 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_sR_223 :
    RegionEmbedded popIterProgram stepRightOnce 223 225 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_sR_225 :
    RegionEmbedded popIterProgram stepRightOnce 225 227 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_wb_227 :
    RegionEmbedded popIterProgram (writeBits [false]) 227 229 := by
  have hacc : ((writeBits [false]).acceptPhase : Nat) = 1 := by
    simp [writeBits]
  refine RegionEmbeddedMulti.toSingle ?_
  rw [show (fun j => if j = (((writeBits [false])).acceptPhase : Nat)
      then some 229 else none) = exitAt 1 229 from by
    funext j; rw [hacc]; rfl]
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_
    (by simp only [unionProgram_numPhases, writeBits_numPhases, List.length_replicate,
          List.length_append, List.length_singleton]
        omega) ?_
  · intro k hk
    have hk' : k < 2 := by
      have := hk
      simp only [writeBits_numPhases, List.length_replicate, List.length_append,
        List.length_singleton] at this
      omega
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

set_option maxRecDepth 8192 in
theorem popIter_region_sL_229 :
    RegionEmbedded popIterProgram stepLeftOnce 229 231 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_sL_231 :
    RegionEmbedded popIterProgram stepLeftOnce 231 233 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_wb_233 :
    RegionEmbedded popIterProgram (writeBits [false]) 233 235 := by
  have hacc : ((writeBits [false]).acceptPhase : Nat) = 1 := by
    simp [writeBits]
  refine RegionEmbeddedMulti.toSingle ?_
  rw [show (fun j => if j = (((writeBits [false])).acceptPhase : Nat)
      then some 235 else none) = exitAt 1 235 from by
    funext j; rw [hacc]; rfl]
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_
    (by simp only [unionProgram_numPhases, writeBits_numPhases, List.length_replicate,
          List.length_append, List.length_singleton]
        omega) ?_
  · intro k hk
    have hk' : k < 2 := by
      have := hk
      simp only [writeBits_numPhases, List.length_replicate, List.length_append,
        List.length_singleton] at this
      omega
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

set_option maxRecDepth 8192 in
theorem popIter_region_scanL_235 :
    RegionEmbedded popIterProgram selfLoopScanLeft 235 237 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_walkL_237 :
    RegionEmbeddedMulti popIterProgram zoneWalkLeft 237 (exitAt 4 242) := by
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [zoneWalkLeft]) ?_
  · intro k hk
    have hk' : k < 5 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

set_option maxRecDepth 8192 in
theorem popIter_region_sL_242 :
    RegionEmbedded popIterProgram stepLeftOnce 242 244 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_scanL1_244 :
    RegionEmbedded popIterProgram selfLoopScanLeftOne 244 246 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_scanL_246 :
    RegionEmbedded popIterProgram selfLoopScanLeft 246 248 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_sR_248 :
    RegionEmbedded popIterProgram stepRightOnce 248 250 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_sR_250 :
    RegionEmbedded popIterProgram stepRightOnce 250 252 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_transfer_252 :
    RegionEmbeddedMulti popIterProgram unaryTransfer 252 (exitAt 8 261) := by
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [unaryTransfer]) ?_
  · intro k hk
    have hk' : k < 9 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

set_option maxRecDepth 8192 in
theorem popIter_region_sR_261 :
    RegionEmbedded popIterProgram stepRightOnce 261 263 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_walkR_263 :
    RegionEmbeddedMulti popIterProgram zoneWalkRight 263 (exitAt 4 269) := by
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [zoneWalkRight]) ?_
  · intro k hk
    have hk' : k < 6 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

set_option maxRecDepth 8192 in
theorem popIter_region_sL_269 :
    RegionEmbedded popIterProgram stepLeftOnce 269 271 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_sL_271 :
    RegionEmbedded popIterProgram stepLeftOnce 271 273 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_sL_273 :
    RegionEmbedded popIterProgram stepLeftOnce 273 275 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_sL_275 :
    RegionEmbedded popIterProgram stepLeftOnce 275 277 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_probe_277 :
    RegionEmbeddedMulti popIterProgram bitProbe 277
      (fun j => if j = 1 then some 315 else if j = 2 then some 280 else none) := by
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [bitProbe]) ?_
  · intro k hk
    have hk' : k < 3 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    split at h
    · cases h; omega
    · split at h
      · cases h; omega
      · cases h

set_option maxRecDepth 8192 in
theorem popIter_region_sR_280 :
    RegionEmbedded popIterProgram stepRightOnce 280 282 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_sR_282 :
    RegionEmbedded popIterProgram stepRightOnce 282 284 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_wb_284 :
    RegionEmbedded popIterProgram (writeBits [false]) 284 286 := by
  have hacc : ((writeBits [false]).acceptPhase : Nat) = 1 := by
    simp [writeBits]
  refine RegionEmbeddedMulti.toSingle ?_
  rw [show (fun j => if j = (((writeBits [false])).acceptPhase : Nat)
      then some 286 else none) = exitAt 1 286 from by
    funext j; rw [hacc]; rfl]
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_
    (by simp only [unionProgram_numPhases, writeBits_numPhases, List.length_replicate,
          List.length_append, List.length_singleton]
        omega) ?_
  · intro k hk
    have hk' : k < 2 := by
      have := hk
      simp only [writeBits_numPhases, List.length_replicate, List.length_append,
        List.length_singleton] at this
      omega
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

set_option maxRecDepth 8192 in
theorem popIter_region_sL_286 :
    RegionEmbedded popIterProgram stepLeftOnce 286 288 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_sL_288 :
    RegionEmbedded popIterProgram stepLeftOnce 288 290 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_walkL_290 :
    RegionEmbeddedMulti popIterProgram zoneWalkLeft 290 (exitAt 4 295) := by
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [zoneWalkLeft]) ?_
  · intro k hk
    have hk' : k < 5 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

set_option maxRecDepth 8192 in
theorem popIter_region_sL_295 :
    RegionEmbedded popIterProgram stepLeftOnce 295 297 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_scanL1_297 :
    RegionEmbedded popIterProgram selfLoopScanLeftOne 297 299 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_wb_299 :
    RegionEmbedded popIterProgram (writeBits [true]) 299 301 := by
  have hacc : ((writeBits [true]).acceptPhase : Nat) = 1 := by
    simp [writeBits]
  refine RegionEmbeddedMulti.toSingle ?_
  rw [show (fun j => if j = (((writeBits [true])).acceptPhase : Nat)
      then some 301 else none) = exitAt 1 301 from by
    funext j; rw [hacc]; rfl]
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_
    (by simp only [unionProgram_numPhases, writeBits_numPhases, List.length_replicate,
          List.length_append, List.length_singleton]
        omega) ?_
  · intro k hk
    have hk' : k < 2 := by
      have := hk
      simp only [writeBits_numPhases, List.length_replicate, List.length_append,
        List.length_singleton] at this
      omega
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

set_option maxRecDepth 8192 in
theorem popIter_region_scanR1_301 :
    RegionEmbedded popIterProgram selfLoopScanRightOne 301 303 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_sR_303 :
    RegionEmbedded popIterProgram stepRightOnce 303 305 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_walkR_305 :
    RegionEmbeddedMulti popIterProgram zoneWalkRight 305 (exitAt 4 311) := by
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [zoneWalkRight]) ?_
  · intro k hk
    have hk' : k < 6 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

set_option maxRecDepth 8192 in
theorem popIter_region_sL_311 :
    RegionEmbedded popIterProgram stepLeftOnce 311 313 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_sL_313 :
    RegionEmbedded popIterProgram stepLeftOnce 313 273 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_sR_315 :
    RegionEmbedded popIterProgram stepRightOnce 315 317 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_sR_317 :
    RegionEmbedded popIterProgram stepRightOnce 317 319 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_wb_319 :
    RegionEmbedded popIterProgram (writeBits [false]) 319 321 := by
  have hacc : ((writeBits [false]).acceptPhase : Nat) = 1 := by
    simp [writeBits]
  refine RegionEmbeddedMulti.toSingle ?_
  rw [show (fun j => if j = (((writeBits [false])).acceptPhase : Nat)
      then some 321 else none) = exitAt 1 321 from by
    funext j; rw [hacc]; rfl]
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_
    (by simp only [unionProgram_numPhases, writeBits_numPhases, List.length_replicate,
          List.length_append, List.length_singleton]
        omega) ?_
  · intro k hk
    have hk' : k < 2 := by
      have := hk
      simp only [writeBits_numPhases, List.length_replicate, List.length_append,
        List.length_singleton] at this
      omega
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

set_option maxRecDepth 8192 in
theorem popIter_region_sL_321 :
    RegionEmbedded popIterProgram stepLeftOnce 321 323 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_sL_323 :
    RegionEmbedded popIterProgram stepLeftOnce 323 325 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_wb_325 :
    RegionEmbedded popIterProgram (writeBits [false]) 325 327 := by
  have hacc : ((writeBits [false]).acceptPhase : Nat) = 1 := by
    simp [writeBits]
  refine RegionEmbeddedMulti.toSingle ?_
  rw [show (fun j => if j = (((writeBits [false])).acceptPhase : Nat)
      then some 327 else none) = exitAt 1 327 from by
    funext j; rw [hacc]; rfl]
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_
    (by simp only [unionProgram_numPhases, writeBits_numPhases, List.length_replicate,
          List.length_append, List.length_singleton]
        omega) ?_
  · intro k hk
    have hk' : k < 2 := by
      have := hk
      simp only [writeBits_numPhases, List.length_replicate, List.length_append,
        List.length_singleton] at this
      omega
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

set_option maxRecDepth 8192 in
theorem popIter_region_scanL_327 :
    RegionEmbedded popIterProgram selfLoopScanLeft 327 329 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_walkL_329 :
    RegionEmbeddedMulti popIterProgram zoneWalkLeft 329 (exitAt 4 334) := by
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [zoneWalkLeft]) ?_
  · intro k hk
    have hk' : k < 5 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

set_option maxRecDepth 8192 in
theorem popIter_region_sL_334 :
    RegionEmbedded popIterProgram stepLeftOnce 334 336 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_scanL1_336 :
    RegionEmbedded popIterProgram selfLoopScanLeftOne 336 338 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_scanL_338 :
    RegionEmbedded popIterProgram selfLoopScanLeft 338 340 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_sR_340 :
    RegionEmbedded popIterProgram stepRightOnce 340 342 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_sR_342 :
    RegionEmbedded popIterProgram stepRightOnce 342 344 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_transfer_344 :
    RegionEmbeddedMulti popIterProgram unaryTransfer 344 (exitAt 8 353) := by
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [unaryTransfer]) ?_
  · intro k hk
    have hk' : k < 9 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

set_option maxRecDepth 8192 in
theorem popIter_region_scanL_353 :
    RegionEmbedded popIterProgram selfLoopScanLeft 353 355 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_sR_355 :
    RegionEmbedded popIterProgram stepRightOnce 355 357 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_sR_357 :
    RegionEmbedded popIterProgram stepRightOnce 357 359 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_wb_359 :
    RegionEmbedded popIterProgram (writeBits [true]) 359 361 := by
  have hacc : ((writeBits [true]).acceptPhase : Nat) = 1 := by
    simp [writeBits]
  refine RegionEmbeddedMulti.toSingle ?_
  rw [show (fun j => if j = (((writeBits [true])).acceptPhase : Nat)
      then some 361 else none) = exitAt 1 361 from by
    funext j; rw [hacc]; rfl]
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_
    (by simp only [unionProgram_numPhases, writeBits_numPhases, List.length_replicate,
          List.length_append, List.length_singleton]
        omega) ?_
  · intro k hk
    have hk' : k < 2 := by
      have := hk
      simp only [writeBits_numPhases, List.length_replicate, List.length_append,
        List.length_singleton] at this
      omega
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

set_option maxRecDepth 8192 in
theorem popIter_region_scanR_361 :
    RegionEmbedded popIterProgram gammaSelfLoopScan 361 363 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_walkR_363 :
    RegionEmbeddedMulti popIterProgram zoneWalkRight 363 (exitAt 4 369) := by
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [zoneWalkRight]) ?_
  · intro k hk
    have hk' : k < 6 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

set_option maxRecDepth 8192 in
theorem popIter_region_sL_369 :
    RegionEmbedded popIterProgram stepLeftOnce 369 371 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_vpush_371 :
    RegionEmbeddedMulti popIterProgram valuePushProgram 371 (exitAt 34 406) := by
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [valuePushProgram]) ?_
  · intro k hk
    have hk' : k < 35 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

set_option maxRecDepth 8192 in
theorem popIter_region_sR_406 :
    RegionEmbedded popIterProgram stepRightOnce 406 408 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_scanR1_408 :
    RegionEmbedded popIterProgram selfLoopScanRightOne 408 410 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_scanR_410 :
    RegionEmbedded popIterProgram gammaSelfLoopScan 410 412 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_scanR1_412 :
    RegionEmbedded popIterProgram selfLoopScanRightOne 412 414 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_wb_414 :
    RegionEmbedded popIterProgram (writeBits [true]) 414 416 := by
  have hacc : ((writeBits [true]).acceptPhase : Nat) = 1 := by
    simp [writeBits]
  refine RegionEmbeddedMulti.toSingle ?_
  rw [show (fun j => if j = (((writeBits [true])).acceptPhase : Nat)
      then some 416 else none) = exitAt 1 416 from by
    funext j; rw [hacc]; rfl]
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_
    (by simp only [unionProgram_numPhases, writeBits_numPhases, List.length_replicate,
          List.length_append, List.length_singleton]
        omega) ?_
  · intro k hk
    have hk' : k < 2 := by
      have := hk
      simp only [writeBits_numPhases, List.length_replicate, List.length_append,
        List.length_singleton] at this
      omega
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

set_option maxRecDepth 8192 in
theorem popIter_region_scanR_416 :
    RegionEmbedded popIterProgram gammaSelfLoopScan 416 418 := by
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

set_option maxRecDepth 8192 in
theorem popIter_region_walkR_418 :
    RegionEmbeddedMulti popIterProgram zoneWalkRight 418 (exitAt 4 424) := by
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [zoneWalkRight]) ?_
  · intro k hk
    have hk' : k < 6 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

set_option maxRecDepth 8192 in
theorem popIter_region_scanR_424 :
    RegionEmbedded popIterProgram gammaSelfLoopScan 424 426 := by
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
