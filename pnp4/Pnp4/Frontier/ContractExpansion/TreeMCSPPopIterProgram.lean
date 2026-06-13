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

Phase layout (`N = 420`): `0–37` entry (stepLeft · 0-scan · `ctrlTopWalk` (tags ↦ the three
`remWalk`s) · 3×`remWalk` (`rem = 1` ↦ the tag track, else ↦ stuck)) · tracks `38`/`83`/`131`
(frame erase · descent · tag write · ascent) · `181` PIPE1 · `257` re-ascent · `269` PIPE2 ·
`345` finish (FM · value push `363–397` · tick · rehome) · `418` out · `419` stuck.

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
  fun j => if j = 5 then some 419 else if j = 6 then some 14 else if j = 7 then some 22
    else if j = 8 then some 30 else if j = 9 then some 419 else none

/-- The per-tag remWalk redirect maps (`rem = 1` ↦ the tag track, dec/reject ↦ stuck). -/
def popRemRedirect (tbase : Nat) : Nat → Option Nat :=
  fun j => if j = 5 then some tbase else if j = 6 then some 419 else if j = 7 then some 419
    else none

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
  else if i < 83 then .run stepLeftOnce 81 (i - 81) (exitAt 1 269)
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
  else if i < 188 then .run bitProbe 185 (i - 185) (fun j => if j = 1 then some 221 else if j = 2 then some 188 else none)
  else if i < 190 then .run stepRightOnce 188 (i - 188) (exitAt 1 190)
  else if i < 192 then .run stepRightOnce 190 (i - 190) (exitAt 1 192)
  else if i < 194 then .run (writeBits [false]) 192 (i - 192) (exitAt 1 194)
  else if i < 196 then .run stepLeftOnce 194 (i - 194) (exitAt 1 196)
  else if i < 198 then .run stepLeftOnce 196 (i - 196) (exitAt 1 198)
  else if i < 203 then .run zoneWalkLeft 198 (i - 198) (exitAt 4 203)
  else if i < 205 then .run selfLoopScanLeftOne 203 (i - 203) (exitAt 1 205)
  else if i < 207 then .run (writeBits [true]) 205 (i - 205) (exitAt 1 207)
  else if i < 209 then .run selfLoopScanRightOne 207 (i - 207) (exitAt 1 209)
  else if i < 211 then .run stepRightOnce 209 (i - 209) (exitAt 1 211)
  else if i < 217 then .run zoneWalkRight 211 (i - 211) (exitAt 4 217)
  else if i < 219 then .run stepLeftOnce 217 (i - 217) (exitAt 1 219)
  else if i < 221 then .run stepLeftOnce 219 (i - 219) (exitAt 1 181)
  else if i < 223 then .run stepRightOnce 221 (i - 221) (exitAt 1 223)
  else if i < 225 then .run stepRightOnce 223 (i - 223) (exitAt 1 225)
  else if i < 227 then .run (writeBits [false]) 225 (i - 225) (exitAt 1 227)
  else if i < 229 then .run stepLeftOnce 227 (i - 227) (exitAt 1 229)
  else if i < 231 then .run stepLeftOnce 229 (i - 229) (exitAt 1 231)
  else if i < 233 then .run (writeBits [false]) 231 (i - 231) (exitAt 1 233)
  else if i < 235 then .run selfLoopScanLeft 233 (i - 233) (exitAt 1 235)
  else if i < 240 then .run zoneWalkLeft 235 (i - 235) (exitAt 4 240)
  else if i < 242 then .run selfLoopScanLeftOne 240 (i - 240) (exitAt 1 242)
  else if i < 244 then .run selfLoopScanLeft 242 (i - 242) (exitAt 1 244)
  else if i < 246 then .run stepRightOnce 244 (i - 244) (exitAt 1 246)
  else if i < 248 then .run stepRightOnce 246 (i - 246) (exitAt 1 248)
  else if i < 257 then .run unaryTransfer 248 (i - 248) (exitAt 8 257)
  else if i < 259 then .run stepRightOnce 257 (i - 257) (exitAt 1 259)
  else if i < 265 then .run zoneWalkRight 259 (i - 259) (exitAt 4 265)
  else if i < 267 then .run stepLeftOnce 265 (i - 265) (exitAt 1 267)
  else if i < 269 then .run stepLeftOnce 267 (i - 267) (exitAt 1 269)
  else if i < 271 then .run stepLeftOnce 269 (i - 269) (exitAt 1 271)
  else if i < 273 then .run stepLeftOnce 271 (i - 271) (exitAt 1 273)
  else if i < 276 then .run bitProbe 273 (i - 273) (fun j => if j = 1 then some 309 else if j = 2 then some 276 else none)
  else if i < 278 then .run stepRightOnce 276 (i - 276) (exitAt 1 278)
  else if i < 280 then .run stepRightOnce 278 (i - 278) (exitAt 1 280)
  else if i < 282 then .run (writeBits [false]) 280 (i - 280) (exitAt 1 282)
  else if i < 284 then .run stepLeftOnce 282 (i - 282) (exitAt 1 284)
  else if i < 286 then .run stepLeftOnce 284 (i - 284) (exitAt 1 286)
  else if i < 291 then .run zoneWalkLeft 286 (i - 286) (exitAt 4 291)
  else if i < 293 then .run selfLoopScanLeftOne 291 (i - 291) (exitAt 1 293)
  else if i < 295 then .run (writeBits [true]) 293 (i - 293) (exitAt 1 295)
  else if i < 297 then .run selfLoopScanRightOne 295 (i - 295) (exitAt 1 297)
  else if i < 299 then .run stepRightOnce 297 (i - 297) (exitAt 1 299)
  else if i < 305 then .run zoneWalkRight 299 (i - 299) (exitAt 4 305)
  else if i < 307 then .run stepLeftOnce 305 (i - 305) (exitAt 1 307)
  else if i < 309 then .run stepLeftOnce 307 (i - 307) (exitAt 1 269)
  else if i < 311 then .run stepRightOnce 309 (i - 309) (exitAt 1 311)
  else if i < 313 then .run stepRightOnce 311 (i - 311) (exitAt 1 313)
  else if i < 315 then .run (writeBits [false]) 313 (i - 313) (exitAt 1 315)
  else if i < 317 then .run stepLeftOnce 315 (i - 315) (exitAt 1 317)
  else if i < 319 then .run stepLeftOnce 317 (i - 317) (exitAt 1 319)
  else if i < 321 then .run (writeBits [false]) 319 (i - 319) (exitAt 1 321)
  else if i < 323 then .run selfLoopScanLeft 321 (i - 321) (exitAt 1 323)
  else if i < 328 then .run zoneWalkLeft 323 (i - 323) (exitAt 4 328)
  else if i < 330 then .run selfLoopScanLeftOne 328 (i - 328) (exitAt 1 330)
  else if i < 332 then .run selfLoopScanLeft 330 (i - 330) (exitAt 1 332)
  else if i < 334 then .run stepRightOnce 332 (i - 332) (exitAt 1 334)
  else if i < 336 then .run stepRightOnce 334 (i - 334) (exitAt 1 336)
  else if i < 345 then .run unaryTransfer 336 (i - 336) (exitAt 8 345)
  else if i < 347 then .run selfLoopScanLeft 345 (i - 345) (exitAt 1 347)
  else if i < 349 then .run stepRightOnce 347 (i - 347) (exitAt 1 349)
  else if i < 351 then .run stepRightOnce 349 (i - 349) (exitAt 1 351)
  else if i < 353 then .run (writeBits [true]) 351 (i - 351) (exitAt 1 353)
  else if i < 355 then .run gammaSelfLoopScan 353 (i - 353) (exitAt 1 355)
  else if i < 361 then .run zoneWalkRight 355 (i - 355) (exitAt 4 361)
  else if i < 363 then .run stepLeftOnce 361 (i - 361) (exitAt 1 363)
  else if i < 398 then .run valuePushProgram 363 (i - 363) (exitAt 34 398)
  else if i < 400 then .run stepRightOnce 398 (i - 398) (exitAt 1 400)
  else if i < 402 then .run selfLoopScanRightOne 400 (i - 400) (exitAt 1 402)
  else if i < 404 then .run gammaSelfLoopScan 402 (i - 402) (exitAt 1 404)
  else if i < 406 then .run selfLoopScanRightOne 404 (i - 404) (exitAt 1 406)
  else if i < 408 then .run (writeBits [true]) 406 (i - 406) (exitAt 1 408)
  else if i < 410 then .run gammaSelfLoopScan 408 (i - 408) (exitAt 1 410)
  else if i < 416 then .run zoneWalkRight 410 (i - 410) (exitAt 4 416)
  else if i < 418 then .run gammaSelfLoopScan 416 (i - 416) (exitAt 1 418)
  else .idle

/-- **The pop iteration machine** (420 phases; start at the settle home `0`, nominal accept at
the home out `418`). -/
def popIterProgram : ConstStatePhasedProgram Unit :=
  unionProgram 420 (by omega) ⟨0, by omega⟩ ⟨418, by omega⟩ popIterAssign

/-! ### The region contracts -/

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

theorem popIter_region_sL_81 :
    RegionEmbedded popIterProgram stepLeftOnce 81 269 := by
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

theorem popIter_region_probe_185 :
    RegionEmbeddedMulti popIterProgram bitProbe 185
      (fun j => if j = 1 then some 221 else if j = 2 then some 188 else none) := by
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

theorem popIter_region_scanL1_203 :
    RegionEmbedded popIterProgram selfLoopScanLeftOne 203 205 := by
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

theorem popIter_region_wb_205 :
    RegionEmbedded popIterProgram (writeBits [true]) 205 207 := by
  have hacc : ((writeBits [true]).acceptPhase : Nat) = 1 := by
    simp [writeBits]
  refine RegionEmbeddedMulti.toSingle ?_
  rw [show (fun j => if j = (((writeBits [true])).acceptPhase : Nat)
      then some 207 else none) = exitAt 1 207 from by
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

theorem popIter_region_scanR1_207 :
    RegionEmbedded popIterProgram selfLoopScanRightOne 207 209 := by
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

theorem popIter_region_sR_209 :
    RegionEmbedded popIterProgram stepRightOnce 209 211 := by
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

theorem popIter_region_walkR_211 :
    RegionEmbeddedMulti popIterProgram zoneWalkRight 211 (exitAt 4 217) := by
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [zoneWalkRight]) ?_
  · intro k hk
    have hk' : k < 6 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

theorem popIter_region_sL_217 :
    RegionEmbedded popIterProgram stepLeftOnce 217 219 := by
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

theorem popIter_region_sL_219 :
    RegionEmbedded popIterProgram stepLeftOnce 219 181 := by
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

theorem popIter_region_sR_221 :
    RegionEmbedded popIterProgram stepRightOnce 221 223 := by
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

theorem popIter_region_wb_225 :
    RegionEmbedded popIterProgram (writeBits [false]) 225 227 := by
  have hacc : ((writeBits [false]).acceptPhase : Nat) = 1 := by
    simp [writeBits]
  refine RegionEmbeddedMulti.toSingle ?_
  rw [show (fun j => if j = (((writeBits [false])).acceptPhase : Nat)
      then some 227 else none) = exitAt 1 227 from by
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

theorem popIter_region_sL_227 :
    RegionEmbedded popIterProgram stepLeftOnce 227 229 := by
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

theorem popIter_region_wb_231 :
    RegionEmbedded popIterProgram (writeBits [false]) 231 233 := by
  have hacc : ((writeBits [false]).acceptPhase : Nat) = 1 := by
    simp [writeBits]
  refine RegionEmbeddedMulti.toSingle ?_
  rw [show (fun j => if j = (((writeBits [false])).acceptPhase : Nat)
      then some 233 else none) = exitAt 1 233 from by
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

theorem popIter_region_scanL_233 :
    RegionEmbedded popIterProgram selfLoopScanLeft 233 235 := by
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

theorem popIter_region_walkL_235 :
    RegionEmbeddedMulti popIterProgram zoneWalkLeft 235 (exitAt 4 240) := by
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [zoneWalkLeft]) ?_
  · intro k hk
    have hk' : k < 5 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

theorem popIter_region_scanL1_240 :
    RegionEmbedded popIterProgram selfLoopScanLeftOne 240 242 := by
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

theorem popIter_region_scanL_242 :
    RegionEmbedded popIterProgram selfLoopScanLeft 242 244 := by
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

theorem popIter_region_sR_244 :
    RegionEmbedded popIterProgram stepRightOnce 244 246 := by
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

theorem popIter_region_sR_246 :
    RegionEmbedded popIterProgram stepRightOnce 246 248 := by
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

theorem popIter_region_transfer_248 :
    RegionEmbeddedMulti popIterProgram unaryTransfer 248 (exitAt 8 257) := by
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [unaryTransfer]) ?_
  · intro k hk
    have hk' : k < 9 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

theorem popIter_region_sR_257 :
    RegionEmbedded popIterProgram stepRightOnce 257 259 := by
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

theorem popIter_region_walkR_259 :
    RegionEmbeddedMulti popIterProgram zoneWalkRight 259 (exitAt 4 265) := by
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [zoneWalkRight]) ?_
  · intro k hk
    have hk' : k < 6 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

theorem popIter_region_sL_265 :
    RegionEmbedded popIterProgram stepLeftOnce 265 267 := by
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

theorem popIter_region_sL_267 :
    RegionEmbedded popIterProgram stepLeftOnce 267 269 := by
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

theorem popIter_region_probe_273 :
    RegionEmbeddedMulti popIterProgram bitProbe 273
      (fun j => if j = 1 then some 309 else if j = 2 then some 276 else none) := by
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

theorem popIter_region_sR_276 :
    RegionEmbedded popIterProgram stepRightOnce 276 278 := by
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

theorem popIter_region_sR_278 :
    RegionEmbedded popIterProgram stepRightOnce 278 280 := by
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

theorem popIter_region_wb_280 :
    RegionEmbedded popIterProgram (writeBits [false]) 280 282 := by
  have hacc : ((writeBits [false]).acceptPhase : Nat) = 1 := by
    simp [writeBits]
  refine RegionEmbeddedMulti.toSingle ?_
  rw [show (fun j => if j = (((writeBits [false])).acceptPhase : Nat)
      then some 282 else none) = exitAt 1 282 from by
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

theorem popIter_region_sL_282 :
    RegionEmbedded popIterProgram stepLeftOnce 282 284 := by
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

theorem popIter_region_sL_284 :
    RegionEmbedded popIterProgram stepLeftOnce 284 286 := by
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

theorem popIter_region_walkL_286 :
    RegionEmbeddedMulti popIterProgram zoneWalkLeft 286 (exitAt 4 291) := by
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [zoneWalkLeft]) ?_
  · intro k hk
    have hk' : k < 5 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

theorem popIter_region_scanL1_291 :
    RegionEmbedded popIterProgram selfLoopScanLeftOne 291 293 := by
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

theorem popIter_region_wb_293 :
    RegionEmbedded popIterProgram (writeBits [true]) 293 295 := by
  have hacc : ((writeBits [true]).acceptPhase : Nat) = 1 := by
    simp [writeBits]
  refine RegionEmbeddedMulti.toSingle ?_
  rw [show (fun j => if j = (((writeBits [true])).acceptPhase : Nat)
      then some 295 else none) = exitAt 1 295 from by
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

theorem popIter_region_scanR1_295 :
    RegionEmbedded popIterProgram selfLoopScanRightOne 295 297 := by
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

theorem popIter_region_sR_297 :
    RegionEmbedded popIterProgram stepRightOnce 297 299 := by
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

theorem popIter_region_walkR_299 :
    RegionEmbeddedMulti popIterProgram zoneWalkRight 299 (exitAt 4 305) := by
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [zoneWalkRight]) ?_
  · intro k hk
    have hk' : k < 6 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

theorem popIter_region_sL_305 :
    RegionEmbedded popIterProgram stepLeftOnce 305 307 := by
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

theorem popIter_region_sL_307 :
    RegionEmbedded popIterProgram stepLeftOnce 307 269 := by
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

theorem popIter_region_sR_309 :
    RegionEmbedded popIterProgram stepRightOnce 309 311 := by
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

theorem popIter_region_sR_311 :
    RegionEmbedded popIterProgram stepRightOnce 311 313 := by
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

theorem popIter_region_wb_313 :
    RegionEmbedded popIterProgram (writeBits [false]) 313 315 := by
  have hacc : ((writeBits [false]).acceptPhase : Nat) = 1 := by
    simp [writeBits]
  refine RegionEmbeddedMulti.toSingle ?_
  rw [show (fun j => if j = (((writeBits [false])).acceptPhase : Nat)
      then some 315 else none) = exitAt 1 315 from by
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

theorem popIter_region_sL_315 :
    RegionEmbedded popIterProgram stepLeftOnce 315 317 := by
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

theorem popIter_region_sL_317 :
    RegionEmbedded popIterProgram stepLeftOnce 317 319 := by
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

theorem popIter_region_scanL_321 :
    RegionEmbedded popIterProgram selfLoopScanLeft 321 323 := by
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

theorem popIter_region_walkL_323 :
    RegionEmbeddedMulti popIterProgram zoneWalkLeft 323 (exitAt 4 328) := by
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [zoneWalkLeft]) ?_
  · intro k hk
    have hk' : k < 5 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

theorem popIter_region_scanL1_328 :
    RegionEmbedded popIterProgram selfLoopScanLeftOne 328 330 := by
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

theorem popIter_region_scanL_330 :
    RegionEmbedded popIterProgram selfLoopScanLeft 330 332 := by
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

theorem popIter_region_sR_332 :
    RegionEmbedded popIterProgram stepRightOnce 332 334 := by
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

theorem popIter_region_sR_334 :
    RegionEmbedded popIterProgram stepRightOnce 334 336 := by
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

theorem popIter_region_transfer_336 :
    RegionEmbeddedMulti popIterProgram unaryTransfer 336 (exitAt 8 345) := by
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [unaryTransfer]) ?_
  · intro k hk
    have hk' : k < 9 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

theorem popIter_region_scanL_345 :
    RegionEmbedded popIterProgram selfLoopScanLeft 345 347 := by
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

theorem popIter_region_sR_347 :
    RegionEmbedded popIterProgram stepRightOnce 347 349 := by
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

theorem popIter_region_sR_349 :
    RegionEmbedded popIterProgram stepRightOnce 349 351 := by
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

theorem popIter_region_wb_351 :
    RegionEmbedded popIterProgram (writeBits [true]) 351 353 := by
  have hacc : ((writeBits [true]).acceptPhase : Nat) = 1 := by
    simp [writeBits]
  refine RegionEmbeddedMulti.toSingle ?_
  rw [show (fun j => if j = (((writeBits [true])).acceptPhase : Nat)
      then some 353 else none) = exitAt 1 353 from by
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

theorem popIter_region_scanR_353 :
    RegionEmbedded popIterProgram gammaSelfLoopScan 353 355 := by
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

theorem popIter_region_walkR_355 :
    RegionEmbeddedMulti popIterProgram zoneWalkRight 355 (exitAt 4 361) := by
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [zoneWalkRight]) ?_
  · intro k hk
    have hk' : k < 6 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

theorem popIter_region_sL_361 :
    RegionEmbedded popIterProgram stepLeftOnce 361 363 := by
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

theorem popIter_region_vpush_363 :
    RegionEmbeddedMulti popIterProgram valuePushProgram 363 (exitAt 34 398) := by
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [valuePushProgram]) ?_
  · intro k hk
    have hk' : k < 35 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

theorem popIter_region_sR_398 :
    RegionEmbedded popIterProgram stepRightOnce 398 400 := by
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

theorem popIter_region_scanR1_400 :
    RegionEmbedded popIterProgram selfLoopScanRightOne 400 402 := by
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

theorem popIter_region_scanR_402 :
    RegionEmbedded popIterProgram gammaSelfLoopScan 402 404 := by
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

theorem popIter_region_scanR1_404 :
    RegionEmbedded popIterProgram selfLoopScanRightOne 404 406 := by
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

theorem popIter_region_wb_406 :
    RegionEmbedded popIterProgram (writeBits [true]) 406 408 := by
  have hacc : ((writeBits [true]).acceptPhase : Nat) = 1 := by
    simp [writeBits]
  refine RegionEmbeddedMulti.toSingle ?_
  rw [show (fun j => if j = (((writeBits [true])).acceptPhase : Nat)
      then some 408 else none) = exitAt 1 408 from by
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

theorem popIter_region_scanR_408 :
    RegionEmbedded popIterProgram gammaSelfLoopScan 408 410 := by
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

theorem popIter_region_walkR_410 :
    RegionEmbeddedMulti popIterProgram zoneWalkRight 410 (exitAt 4 416) := by
  refine unionProgram_embedded _ _ _ _ _ _ _ _ ?_ (by simp [zoneWalkRight]) ?_
  · intro k hk
    have hk' : k < 6 := hk
    interval_cases k <;> rfl
  · intro j nxt h
    unfold exitAt at h
    split at h
    · cases h; omega
    · cases h

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

end ContractExpansion
end Frontier
end Pnp4
