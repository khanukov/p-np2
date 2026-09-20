import Complexity.TMVerifier.TuringToolkit.GateNBodyRound

/-!
# GN-E2-3b arbitrary body induction and first-record `recordDone` (2026-09-20)

**Progress classification: infrastructure, not P-vs-NP mainline progress.**

This module adds no `GNState` constructor, no `gnTransition` row, no machine,
no clock, no encoder, no request-dependent runtime state and no runtime
geometry.  It contributes exactly two execution results on top of GN-E2-3a —
the arbitrary proof-level induction that iterates
`gnCS_bodyRound_iteration_exact` over a finite source body list and terminates
with `gnCS_bodyFinishRound_recordDone_exact`, and the composition of that
induction with the real GN-E2-2 initial execution — together with the pure
frame-split and schedule arithmetic those two need.

The concrete capstone is genuine `TM.runConfig (M := GNM)` execution from
`GNM.initialConfig (gnPoint (encodeGN r))`, for the actually selected first
gate `g` supplied by `hg : r.program.gates[0]? = some g`.  Its endpoint pins an
exact accumulated schedule, the literal `.recordDone` state, an exact head, and
the complete physical tape: the original GN word is restored verbatim and the
scratch region holds exactly `(gnRecordFrames .cursor g).map gnInstallImage`
followed by the retained blank frontier.  No endpoint is weakened to a wrapper
predicate.

Deliberately *not* here, and claimed nowhere: any continuation from
`recordDone`, any values/tail writer, any launch, delegation, commit, next-gate
loop, verdict, acceptance, total installer clock, or total evaluator claim.  In
particular the pure evaluator `evalGNProgram` is **not** executed by this
machine: at this endpoint the machine has only relocated the selected record's
frames, and `gnFirstRecordDoneConfig_structure`'s semantic conjuncts are
statements about the *pure* request determined by `g`, not about anything the
machine has computed.  E2-4 owns continuation from `recordDone`.

This driver opens no new ingress boundary: it introduces no state and no
transition row, and every row it contributes is a GN-E2-3a round (the
real-input capstone additionally replays GN-E2-2's already-audited prefix
unchanged).  The malformed/reserved-code rejection at the only boundary it uses
is already covered exactly by `gnCS_install_exit_reserved1101_reject_five` and
`gnCS_install_exit_reserved1101_reject_stable`, so no rejection probe is
duplicated here.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

open Pnp3.Internal.PsubsetPpoly.TM.FrameScan
open Encoding

/-! ## Exact record-body frame split -/

/-- The serialized body of one gate record: the unary tag run and the two
absolute-index runs, without the leading marker and without the closing
`finish`.  Every frame is an ordinary `GNInstallBody` frame. -/
def gnGateBodyFrames {n : Nat} (g : SLGate n) : List G1Frame :=
  List.replicate (gnGateFields g).1.units .tag ++ [.argSep] ++
    List.replicate (gnGateFields g).2.1 .index ++ [.argSep] ++
    List.replicate (gnGateFields g).2.2 .index

/-- `gnGateBodyFrames` after its mandatory leading `tag`.  Every unary tag run
has at least one unit, so this is exactly the remaining body. -/
def gnGateBodyTail {n : Nat} (g : SLGate n) : List G1Frame :=
  List.replicate ((gnGateFields g).1.units - 1) .tag ++ [.argSep] ++
    List.replicate (gnGateFields g).2.1 .index ++ [.argSep] ++
    List.replicate (gnGateFields g).2.2 .index

/-- Source frames of a nonempty stage-zero GN word strictly after the first
record's closing `finish`: every later gate record, then the terminal
separator, output slot, and word-final finish.  It does not depend on which
gate was selected, so it takes no gate argument. -/
def gnFirstRecordTail (r : GNProgram) : List G1Frame :=
  gnRecordsFrames .bof (r.program.gates.drop 1) ++
    [.separator, .output false, .finish]

/-- Every record body starts with a `tag`, because `G1Tag.units` is never
zero. -/
theorem gnGateBodyFrames_cons {n : Nat} (g : SLGate n) :
    gnGateBodyFrames g = G1Frame.tag :: gnGateBodyTail g := by
  cases g <;>
    simp [gnGateBodyFrames, gnGateBodyTail, gnGateFields, G1Tag.units,
      List.replicate_succ]

/-- One record's full frame list splits into marker, body, and closing
`finish`. -/
theorem gnRecordFrames_cursor_split {n : Nat} (g : SLGate n) :
    gnRecordFrames .cursor g =
      G1Frame.cursor :: gnGateBodyFrames g ++ [G1Frame.finish] := by
  simp [gnRecordFrames, g1RecordFrames, gnGateBodyFrames, List.append_assoc]

/-- The record body contains only ordinary serialized body frames. -/
theorem gnGateBodyFrames_body {n : Nat} (g : SLGate n) :
    ∀ frame ∈ gnGateBodyFrames g, GNInstallBody frame := by
  intro frame hframe
  simp only [gnGateBodyFrames, List.mem_append, List.mem_replicate,
    List.mem_cons, List.not_mem_nil, or_false, GNInstallBody] at hframe ⊢
  tauto

/-- Installing a record body is the identity: no body frame is a boundary
frame, so the scratch image of the body is the body itself. -/
theorem gnGateBodyFrames_map_image {n : Nat} (g : SLGate n) :
    (gnGateBodyFrames g).map gnInstallImage = gnGateBodyFrames g := by
  have h : (gnGateBodyFrames g).map gnInstallImage =
      (gnGateBodyFrames g).map id :=
    List.map_congr_left (fun frame hframe =>
      gnInstallImage_laws.2.2.1 frame (gnGateBodyFrames_body g frame hframe))
  rw [h, List.map_id]

/-- Exact source split of the forward middle at the selected first gate: the
first record's body, its closing `finish`, and everything after it.  The split
is taken from the actually selected `g`, not from an unrelated record. -/
theorem gnFirstRecordMiddle_split {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    gnFirstRecordMiddle r =
      gnGateBodyFrames g ++ G1Frame.finish :: gnFirstRecordTail r := by
  rcases r with ⟨inputs, ⟨gates⟩⟩
  cases gates with
  | nil => simp at hg
  | cons first rest =>
      simp at hg
      subst g
      simp [gnFirstRecordMiddle, gnFirstRecordInner, gnFirstRecordTail,
        gnRecordsFrames, gnFieldRecordsFrames, g1RecordFrames,
        gnGateBodyFrames, List.append_assoc]

/-- The post-record source sits inside the forward middle, so its frames are
already known to be admissible shuttle sources. -/
theorem gnFirstRecordTail_admissible {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    ∀ frame ∈ gnFirstRecordTail r, GNInstallAdmissible frame := by
  intro frame hframe
  refine (gnFirstRecord_copyShuttle_handoff hg).2.1 frame ?_
  rw [gnFirstRecordMiddle_split hg]
  exact List.mem_append_right _ (List.mem_cons_of_mem _ hframe)

/-! ## Accumulated driver schedule -/

/-- Accumulated body schedule: one ordinary `gnBodyRoundSteps` round per source
body frame, then exactly one `gnBodyTerminalSteps` round for the record's
`finish`.  The shuttle distance is a parameter because it is invariant along
the whole driver: each source frame removed from the unprocessed suffix becomes
one mapped scratch frame. -/
def gnBodyDriverSteps (rounds distance : Nat) : Nat :=
  rounds * gnBodyRoundSteps distance + gnBodyTerminalSteps distance

private theorem gnBodyDriverSteps_succ (rounds distance : Nat) :
    gnBodyDriverSteps (rounds + 1) distance =
      gnBodyRoundSteps distance + gnBodyDriverSteps rounds distance := by
  simp only [gnBodyDriverSteps, Nat.succ_mul]
  omega

/-- Exact arithmetic provenance and the two recurrences the induction uses. -/
theorem gnBodyDriverSteps_provenance (rounds distance : Nat) :
    gnBodyDriverSteps rounds distance =
        rounds * (8 * distance + 30) + (8 * distance + 31) ∧
      gnBodyDriverSteps 0 distance = gnBodyTerminalSteps distance ∧
      gnBodyDriverSteps (rounds + 1) distance =
        gnBodyRoundSteps distance + gnBodyDriverSteps rounds distance :=
  ⟨by simp [gnBodyDriverSteps, gnBodyRoundSteps, gnBodyTerminalSteps],
    by simp [gnBodyDriverSteps], gnBodyDriverSteps_succ rounds distance⟩

/-- The driver's final room bound implies the room bound of its first round.
Room shrinks monotonically as processed source frames move into `done`, so the
driver states only the strongest of the bounds it needs. -/
theorem gnBodyDriver_room_start {n : Nat} {fixed done : List G1Frame}
    {current : G1Frame} {body tail seed : List G1Frame}
    (hroom : 4 * ((fixed ++ done).length + (current :: body).length +
      (gnBodyRoundMiddle done (body ++ G1Frame.finish :: tail) seed).length +
        2) < GNM.tapeLength n) :
    4 * ((fixed ++ done).length +
      (gnBodyRoundMiddle done (body ++ G1Frame.finish :: tail) seed).length +
        2) < GNM.tapeLength n := by
  have hlen : (current :: body).length = body.length + 1 := rfl
  omega

/-! ## Arbitrary proof-level body induction -/

private theorem gnInstallExitContinue_of_body {frame : G1Frame}
    (hframe : GNInstallBody frame) :
    GNInstallExitContinue (.carried frame) := by
  rcases hframe with rfl | rfl | rfl <;> trivial

private theorem gnInstallAdmissible_of_body {frame : G1Frame}
    (hframe : GNInstallBody frame) : GNInstallAdmissible frame := by
  rcases hframe with rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩

private theorem gnBodyDriver_middle_step {done tail seed : List G1Frame}
    {current : G1Frame} (hcurrent : GNInstallBody current)
    (hmiddle : ∀ frame ∈ tail ++ seed ++ done.map gnInstallImage,
      GNInstallAdmissible frame) :
    ∀ frame ∈ tail ++ seed ++ (done ++ [current]).map gnInstallImage,
      GNInstallAdmissible frame := by
  intro frame hframe
  rcases List.mem_append.1 hframe with h | h
  · exact hmiddle frame (List.mem_append_left _ h)
  · rw [List.map_append] at h
    rcases List.mem_append.1 h with h | h
    · exact hmiddle frame (List.mem_append_right _ h)
    · simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
        or_false] at h
      subst h
      rw [gnInstallImage_laws.2.2.1 current hcurrent]
      exact gnInstallAdmissible_of_body hcurrent

private theorem gnBodyDriver_invariant {n : Nat} {fixed done : List G1Frame}
    {current : G1Frame} {todo tail seed : List G1Frame}
    {previous : GNInstallAux} (hprevious : GNInstallExitContinue previous)
    (hsource : GNBodyRoundSource current)
    (htodo : ∀ frame ∈ todo, GNInstallAdmissible frame)
    (hmiddle : ∀ frame ∈ tail ++ seed ++ done.map gnInstallImage,
      GNInstallAdmissible frame)
    (hroom : 4 * ((fixed ++ done).length +
      (gnBodyRoundMiddle done todo seed).length + 2) < GNM.tapeLength n) :
    GNBodyRoundInvariant n fixed done current todo seed previous := by
  refine ⟨hprevious, hsource, ?_, hroom⟩
  intro frame hframe
  rw [gnBodyRoundMiddle] at hframe
  rcases List.mem_append.1 hframe with h | h
  · rcases List.mem_append.1 h with h | h
    · exact htodo frame h
    · exact hmiddle frame (List.mem_append_left _ (List.mem_append_right _ h))
  · exact hmiddle frame (List.mem_append_right _ h)

private theorem gnCS_bodyDriver_run (n : Nat) (fixed tail seed : List G1Frame)
    (htail : ∀ frame ∈ tail, GNInstallAdmissible frame) :
    ∀ body : List G1Frame, (∀ frame ∈ body, GNInstallBody frame) →
      ∀ (done : List G1Frame) (current : G1Frame) (previous : GNInstallAux),
        GNInstallExitContinue previous → GNInstallBody current →
        (∀ frame ∈ tail ++ seed ++ done.map gnInstallImage,
          GNInstallAdmissible frame) →
        ∀ hroom : 4 * ((fixed ++ done).length + (current :: body).length +
            (gnBodyRoundMiddle done (body ++ G1Frame.finish :: tail)
              seed).length + 2) < GNM.tapeLength n,
          TM.runConfig (M := GNM)
              (gnBodyRoundConfig n fixed done current
                (body ++ G1Frame.finish :: tail) seed [] previous
                (gnBodyDriver_room_start hroom))
              (gnBodyDriverSteps (current :: body).length
                (gnBodyRoundMiddle done (body ++ G1Frame.finish :: tail)
                  seed).length) =
            gnCopyShuttle.cfg n
              (4 * (fixed ++ (done ++ current :: body)).length + 4) (by
                change 4 * (fixed ++ (done ++ current :: body)).length + 4 <
                  GNM.tapeLength n
                have h := hroom
                simp only [List.length_append, List.length_cons] at h ⊢
                omega)
              (frameListTape
                (((fixed ++ (done ++ current :: body)) ++ G1Frame.finish ::
                  gnBodyRoundMiddle (done ++ current :: body) tail seed ++
                    G1Frame.separator :: G1Frame.blank :: []).flatMap
                      G1Frame.bits))
              .recordDone := by
  intro body
  induction body with
  | nil =>
      intro _ done current previous hprevious hcurrent hmiddle hroom
      have hconst := gnBodyRoundMiddle_length_constant done tail seed current
        G1Frame.finish
      have hroom0 : 4 * ((fixed ++ done).length +
          (gnBodyRoundMiddle done (G1Frame.finish :: tail) seed).length + 2) <
            GNM.tapeLength n := by
        have h := hroom
        simp only [List.nil_append, List.length_cons, List.length_nil] at h
        omega
      have hnextRoom : 4 * ((fixed ++ (done ++ [current])).length +
          (gnBodyRoundMiddle (done ++ [current]) tail seed).length + 2) <
            GNM.tapeLength n := by
        have h := hroom
        simp only [List.nil_append, List.length_cons, List.length_nil,
          List.length_append] at h ⊢
        omega
      have hadm : ∀ frame ∈ G1Frame.finish :: tail,
          GNInstallAdmissible frame := by
        intro frame hframe
        rcases List.mem_cons.1 hframe with rfl | hframe
        · exact ⟨by decide, by decide⟩
        · exact htail frame hframe
      have hinv : GNBodyRoundInvariant n fixed done current
          (G1Frame.finish :: tail) seed previous :=
        gnBodyDriver_invariant hprevious (Or.inl hcurrent) hadm hmiddle hroom0
      have hinv2 : GNBodyRoundInvariant n fixed (done ++ [current]) .finish tail
          seed (.carried current) :=
        gnBodyDriver_invariant (gnInstallExitContinue_of_body hcurrent)
          (Or.inr rfl) htail (gnBodyDriver_middle_step hcurrent hmiddle)
          hnextRoom
      have hstep := gnCS_bodyRound_iteration_exact n fixed done current
        G1Frame.finish tail seed previous hinv hcurrent hnextRoom
      have hfinish := gnCS_bodyFinishRound_recordDone_exact n fixed
        (done ++ [current]) tail seed [] (.carried current) hinv2
      have hsched : gnBodyDriverSteps (current :: ([] : List G1Frame)).length
            (gnBodyRoundMiddle done (([] : List G1Frame) ++
              G1Frame.finish :: tail) seed).length =
          gnBodyRoundSteps
              (gnBodyRoundMiddle done (G1Frame.finish :: tail) seed).length +
            gnBodyTerminalSteps
              (gnBodyRoundMiddle (done ++ [current]) tail seed).length := by
        simp only [List.nil_append, List.length_cons, List.length_nil,
          ← hconst, gnBodyDriverSteps]
        omega
      have hcfg : gnBodyRoundConfig n fixed done current
            (([] : List G1Frame) ++ G1Frame.finish :: tail) seed [] previous
            (gnBodyDriver_room_start hroom) =
          gnBodyRoundConfig n fixed done current (G1Frame.finish :: tail) seed []
            previous hinv.room := rfl
      rw [hsched, runConfig_add, hcfg, hstep]
      exact hfinish
  | cons next later ih =>
      intro hbody done current previous hprevious hcurrent hmiddle hroom
      have hlater : ∀ frame ∈ later, GNInstallBody frame := fun frame hframe =>
        hbody frame (List.mem_cons_of_mem _ hframe)
      have hnext : GNInstallBody next := hbody next (by simp)
      have hconst := gnBodyRoundMiddle_length_constant done
        (later ++ G1Frame.finish :: tail) seed current next
      have hadm : ∀ frame ∈ next :: (later ++ G1Frame.finish :: tail),
          GNInstallAdmissible frame := by
        intro frame hframe
        rcases List.mem_cons.1 hframe with rfl | hframe
        · exact gnInstallAdmissible_of_body hnext
        rcases List.mem_append.1 hframe with hframe | hframe
        · exact gnInstallAdmissible_of_body (hlater frame hframe)
        rcases List.mem_cons.1 hframe with rfl | hframe
        · exact ⟨by decide, by decide⟩
        · exact htail frame hframe
      have hroom0 : 4 * ((fixed ++ done).length +
          (gnBodyRoundMiddle done (next :: (later ++ G1Frame.finish :: tail))
            seed).length + 2) < GNM.tapeLength n := by
        have h := hroom
        simp only [List.cons_append, List.length_cons] at h ⊢
        omega
      have hinv : GNBodyRoundInvariant n fixed done current
          (next :: (later ++ G1Frame.finish :: tail)) seed previous :=
        gnBodyDriver_invariant hprevious (Or.inl hcurrent) hadm hmiddle hroom0
      have hA : (fixed ++ (done ++ [current])).length =
          (fixed ++ done).length + 1 := by
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      have hC : (current :: next :: later).length =
          (next :: later).length + 1 := rfl
      have hD : (gnBodyRoundMiddle done ((next :: later) ++
            G1Frame.finish :: tail) seed).length =
          (gnBodyRoundMiddle (done ++ [current])
            (later ++ G1Frame.finish :: tail) seed).length := hconst
      have hnextRoom : 4 * ((fixed ++ (done ++ [current])).length +
          (next :: later).length +
          (gnBodyRoundMiddle (done ++ [current])
            (later ++ G1Frame.finish :: tail) seed).length + 2) <
            GNM.tapeLength n := by
        omega
      have hroundRoom : 4 * ((fixed ++ (done ++ [current])).length +
          (gnBodyRoundMiddle (done ++ [current])
            (later ++ G1Frame.finish :: tail) seed).length + 2) <
            GNM.tapeLength n := by
        have hlen : (next :: later).length = later.length + 1 := rfl
        omega
      have hstep := gnCS_bodyRound_iteration_exact n fixed done current next
        (later ++ G1Frame.finish :: tail) seed previous hinv hcurrent hroundRoom
      have hrec := ih hlater (done ++ [current]) next (.carried current)
        (gnInstallExitContinue_of_body hcurrent) hnext
        (gnBodyDriver_middle_step hcurrent hmiddle) hnextRoom
      have hsched : gnBodyDriverSteps (current :: next :: later).length
            (gnBodyRoundMiddle done ((next :: later) ++
              G1Frame.finish :: tail) seed).length =
          gnBodyRoundSteps
              (gnBodyRoundMiddle done
                (next :: (later ++ G1Frame.finish :: tail)) seed).length +
            gnBodyDriverSteps (next :: later).length
              (gnBodyRoundMiddle (done ++ [current])
                (later ++ G1Frame.finish :: tail) seed).length := by
        have h1 : (current :: next :: later).length =
            (next :: later).length + 1 := rfl
        have h2 : (next :: later) ++ G1Frame.finish :: tail =
            next :: (later ++ G1Frame.finish :: tail) := rfl
        rw [h1, h2, ← hconst, gnBodyDriverSteps_succ]
      have hcfg : gnBodyRoundConfig n fixed done current
            ((next :: later) ++ G1Frame.finish :: tail) seed [] previous
            (gnBodyDriver_room_start hroom) =
          gnBodyRoundConfig n fixed done current
            (next :: (later ++ G1Frame.finish :: tail)) seed [] previous
            hinv.room := rfl
      have hlist : (done ++ [current]) ++ next :: later =
          done ++ current :: next :: later := by
        simp
      rw [hsched, runConfig_add, hcfg, hstep]
      refine hrec.trans ?_
      apply Configuration.ext_of_components
      · rfl
      · apply Fin.ext
        change 4 * (fixed ++ ((done ++ [current]) ++ next :: later)).length + 4 =
          4 * (fixed ++ (done ++ current :: next :: later)).length + 4
        rw [hlist]
      · change frameListTape _ = frameListTape _
        rw [hlist]

/-- **Arbitrary body induction.**  From any proof-level exit boundary carrying a
continuing payload, with `current :: body` an arbitrary finite list of ordinary
source body frames followed by the record's `finish`, the machine runs exactly
`gnBodyDriverSteps (current :: body).length d` rows of genuine
`TM.runConfig (M := GNM)` execution and stops in the literal `recordDone` state.

The endpoint is a complete physical configuration: the head is exactly p0 of
the frame just past the record's `finish`, the source
`fixed ++ done ++ current :: body ++ finish :: tail` is restored verbatim, the
scratch region is `seed ++ (done ++ current :: body).map gnInstallImage ++
[separator]` in processing order, and one blank frontier is retained.  The full
tape equality is stated physically; nothing is weakened to a wrapper
predicate. -/
theorem gnCS_bodyDriver_recordDone_exact (n : Nat)
    (fixed done : List G1Frame) (current : G1Frame)
    (body tail seed : List G1Frame) (previous : GNInstallAux)
    (hprevious : GNInstallExitContinue previous)
    (hcurrent : GNInstallBody current)
    (hbody : ∀ frame ∈ body, GNInstallBody frame)
    (hmiddle : ∀ frame ∈ tail ++ seed ++ done.map gnInstallImage,
      GNInstallAdmissible frame)
    (hroom : 4 * ((fixed ++ done).length + (current :: body).length +
      (gnBodyRoundMiddle done (body ++ G1Frame.finish :: tail) seed).length +
        2) < GNM.tapeLength n) :
    TM.runConfig (M := GNM)
        (gnBodyRoundConfig n fixed done current (body ++ G1Frame.finish :: tail)
          seed [] previous (gnBodyDriver_room_start hroom))
        (gnBodyDriverSteps (current :: body).length
          (gnBodyRoundMiddle done (body ++ G1Frame.finish :: tail)
            seed).length) =
      gnCopyShuttle.cfg n (4 * (fixed ++ (done ++ current :: body)).length + 4)
        (by
          change 4 * (fixed ++ (done ++ current :: body)).length + 4 <
            GNM.tapeLength n
          have h := hroom
          simp only [List.length_append, List.length_cons] at h ⊢
          omega)
        (frameListTape
          (((fixed ++ (done ++ current :: body)) ++ G1Frame.finish ::
            gnBodyRoundMiddle (done ++ current :: body) tail seed ++
              G1Frame.separator :: G1Frame.blank :: []).flatMap G1Frame.bits))
        .recordDone :=
  gnCS_bodyDriver_run n fixed tail seed
    (fun frame hframe =>
      hmiddle frame (List.mem_append_left _ (List.mem_append_left _ hframe)))
    body hbody done current previous hprevious hcurrent hmiddle hroom

/-! ## Real-input first-record capstone -/

/-- Full real-initial schedule through the exact first `recordDone`:
GN-E2-2's seed schedule, then one ordinary round per record-body frame, then
the terminal round. -/
def gnFirstRecordDoneSteps (r : GNProgram) (g : SLGate r.inputs.length) :
    Nat :=
  gnBofSeedSteps r +
    gnBodyDriverSteps (gnGateBodyFrames g).length (gnFirstRecordMiddle r).length

/-- Exact arithmetic provenance of the real-initial schedule. -/
theorem gnFirstRecordDoneSteps_provenance (r : GNProgram)
    (g : SLGate r.inputs.length) :
    gnFirstRecordDoneSteps r g =
      gnBofSeedSteps r +
        ((gnGateBodyFrames g).length *
            (8 * (gnFirstRecordMiddle r).length + 30) +
          (8 * (gnFirstRecordMiddle r).length + 31)) := by
  simp [gnFirstRecordDoneSteps, gnBodyDriverSteps, gnBodyRoundSteps,
    gnBodyTerminalSteps]

private theorem gnGateBodyFrames_length_cons {n : Nat} (g : SLGate n) :
    (G1Frame.tag :: gnGateBodyTail g).length = (gnGateBodyFrames g).length := by
  rw [gnGateBodyFrames_cons g]

private theorem gnFirstRecordMiddle_length_split {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    (gnFirstRecordMiddle r).length =
      (gnGateBodyFrames g).length + 1 + (gnFirstRecordTail r).length := by
  rw [gnFirstRecordMiddle_split hg]
  simp only [List.length_append, List.length_cons]
  omega

private theorem gnFirstRecordDone_middle_length {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    (gnBodyRoundMiddle ([] : List G1Frame)
        (gnGateBodyTail g ++ G1Frame.finish :: gnFirstRecordTail r)
        [G1Frame.bof]).length = (gnFirstRecordMiddle r).length := by
  have h1 := gnFirstRecordMiddle_length_split hg
  have h2 : (gnGateBodyFrames g).length = (gnGateBodyTail g).length + 1 := by
    rw [gnGateBodyFrames_cons g]
    simp
  have h3 : (gnBodyRoundMiddle ([] : List G1Frame)
      (gnGateBodyTail g ++ G1Frame.finish :: gnFirstRecordTail r)
      [G1Frame.bof]).length =
      (gnGateBodyTail g).length + 1 + (gnFirstRecordTail r).length + 1 := by
    simp only [gnBodyRoundMiddle, List.map_nil, List.append_nil,
      List.length_append, List.length_cons, List.length_nil]
    omega
  omega

private theorem gnEncodeGN_length_split {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    (encodeGN r).length =
      4 * (gnRecordsStart r + 1 + (gnFirstRecordMiddle r).length) := by
  have hs := encodeGNFrames_firstRecord_split hg
  rw [encodeGN_length, hs.1]
  simp only [List.length_append, List.length_cons, gnFirstRecordMiddle,
    List.length_nil]
  omega

private theorem gnRecordSize_eq_body {n : Nat} (g : SLGate n) :
    gnRecordSize (gnGateFields g) = (gnGateBodyFrames g).length + 2 := by
  simp only [gnRecordSize, gnGateBodyFrames, List.length_append,
    List.length_replicate, List.length_cons, List.length_nil]
  omega

private theorem gnFirstRecordDone_head_lt {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    4 * (gnRecordsStart r + gnRecordSize (gnGateFields g)) <
      GNM.tapeLength (encodeGN r).length := by
  have hlen := gnFirstRecordMiddle_length_split hg
  have hn := gnEncodeGN_length_split hg
  have hsize := gnRecordSize_eq_body g
  have hclock : 0 < gnClock (encodeGN r).length := by
    unfold gnClock g1Clock
    omega
  change 4 * (gnRecordsStart r + gnRecordSize (gnGateFields g)) <
    (encodeGN r).length + gnClock (encodeGN r).length + 1
  omega

/-- Exact real-input first-record endpoint.  The GN word is restored verbatim,
the scratch region is exactly the installed image of the selected record, and
one blank frontier is retained. -/
def gnFirstRecordDoneConfig (r : GNProgram) (g : SLGate r.inputs.length)
    (hg : r.program.gates[0]? = some g) :
    Configuration (M := GNM) (encodeGN r).length where
  state := ⟨(0 : Fin 1), .recordDone⟩
  head := ⟨4 * (gnRecordsStart r + gnRecordSize (gnGateFields g)),
    gnFirstRecordDone_head_lt hg⟩
  tape := frameListTape
    ((encodeGNFrames r ++ (gnRecordFrames .cursor g).map gnInstallImage ++
      [G1Frame.blank]).flatMap G1Frame.bits)

private theorem gnFirstRecordDone_room {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    4 * (((gnLocatePrefix r ++ [G1Frame.cursor]) ++
        ([] : List G1Frame)).length +
        (G1Frame.tag :: gnGateBodyTail g).length +
        (gnBodyRoundMiddle ([] : List G1Frame)
          (gnGateBodyTail g ++ G1Frame.finish :: gnFirstRecordTail r)
          [G1Frame.bof]).length + 2) <
      GNM.tapeLength (encodeGN r).length := by
  have hpre := (encodeGNFrames_firstRecord_split hg).2.1
  have hlen := gnFirstRecordMiddle_length_split hg
  have hn := gnEncodeGN_length_split hg
  have hbody := gnGateBodyFrames_length_cons g
  have hmid := gnFirstRecordDone_middle_length hg
  have hfixed : ((gnLocatePrefix r ++ [G1Frame.cursor]) ++
      ([] : List G1Frame)).length = (gnLocatePrefix r).length + 1 := by
    simp
  have hsquare : (encodeGN r).length + 1 ≤ ((encodeGN r).length + 1) ^ 2 := by
    rw [pow_two]
    exact Nat.le_mul_of_pos_left _ (by omega)
  have hclock : gnClock (encodeGN r).length =
      512 * ((encodeGN r).length + 1) ^ 2 + 512 := rfl
  change 4 * (((gnLocatePrefix r ++ [G1Frame.cursor]) ++
      ([] : List G1Frame)).length + (G1Frame.tag :: gnGateBodyTail g).length +
      (gnBodyRoundMiddle ([] : List G1Frame)
        (gnGateBodyTail g ++ G1Frame.finish :: gnFirstRecordTail r)
        [G1Frame.bof]).length + 2) <
    (encodeGN r).length + gnClock (encodeGN r).length + 1
  omega

private theorem gnBofSeed_eq_bodyRoundConfig {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    gnBofSeedConfig r g hg =
      gnBodyRoundConfig (encodeGN r).length
        (gnLocatePrefix r ++ [G1Frame.cursor]) [] G1Frame.tag
        (gnGateBodyTail g ++ G1Frame.finish :: gnFirstRecordTail r)
        [G1Frame.bof] [] (.carried .cursor)
        (gnBodyDriver_room_start (gnFirstRecordDone_room hg)) := by
  have hmiddle : G1Frame.tag ::
      (gnGateBodyTail g ++ G1Frame.finish :: gnFirstRecordTail r) =
      gnFirstRecordMiddle r := by
    rw [gnFirstRecordMiddle_split hg, gnGateBodyFrames_cons g]
    simp
  apply Configuration.ext_of_components
  · rfl
  · apply Fin.ext
    have hpre := (encodeGNFrames_firstRecord_split hg).2.1
    change 4 * (gnRecordsStart r + 1) =
      4 * ((gnLocatePrefix r ++ [G1Frame.cursor]) ++
        ([] : List G1Frame)).length
    simp only [List.append_nil, List.length_append, List.length_cons,
      List.length_nil]
    omega
  · change frameListTape _ = frameListTape _
    rw [show gnBodyRoundFrames (gnLocatePrefix r ++ [G1Frame.cursor]) []
          G1Frame.tag (gnGateBodyTail g ++ G1Frame.finish :: gnFirstRecordTail r)
          [G1Frame.bof] [] =
        (gnLocatePrefix r ++ G1Frame.cursor :: gnFirstRecordMiddle r ++
          [G1Frame.bof, G1Frame.blank]) ++ [G1Frame.blank] from by
      rw [gnBodyRoundFrames, gnBodyRoundMiddle, ← hmiddle]
      simp [List.append_assoc]]
    simpa only [g1FrameCodec_bits] using
      (frameListTape_append_blank
        (L := GNM.tapeLength (encodeGN r).length) g1FrameCodec
        (gnLocatePrefix r ++ G1Frame.cursor :: gnFirstRecordMiddle r ++
          [G1Frame.bof, G1Frame.blank]) G1Frame.blank rfl)

private theorem gnFirstRecordDone_frames {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    ((gnLocatePrefix r ++ [G1Frame.cursor]) ++
        (([] : List G1Frame) ++ G1Frame.tag :: gnGateBodyTail g)) ++
      G1Frame.finish ::
        gnBodyRoundMiddle (([] : List G1Frame) ++
          G1Frame.tag :: gnGateBodyTail g) (gnFirstRecordTail r)
          [G1Frame.bof] ++
        G1Frame.separator :: G1Frame.blank :: [] =
      encodeGNFrames r ++ (gnRecordFrames .cursor g).map gnInstallImage ++
        [G1Frame.blank] := by
  have hbodyList : (([] : List G1Frame) ++ G1Frame.tag :: gnGateBodyTail g) =
      gnGateBodyFrames g := by
    rw [List.nil_append, ← gnGateBodyFrames_cons g]
  have hshape : encodeGNFrames r =
      gnLocatePrefix r ++ G1Frame.cursor :: gnFirstRecordMiddle r := by
    simpa [gnFirstRecordMiddle, List.append_assoc] using
      (encodeGNFrames_firstRecord_split hg).1
  rw [hbodyList, gnBodyRoundMiddle, hshape, gnFirstRecordMiddle_split hg,
    gnRecordFrames_cursor_split]
  simp [gnGateBodyFrames_map_image, gnInstallImage, List.append_assoc]

/-- **Real-input capstone.**  Starting from the genuine
`GNM.initialConfig (gnPoint (encodeGN r))` and using the actually selected first
gate `g`, the machine runs exactly `gnFirstRecordDoneSteps r g` rows of genuine
`TM.runConfig (M := GNM)` execution and stops in the exact first-record
`recordDone` configuration.  Execution stops there; continuation from
`recordDone` belongs to E2-4. -/
theorem gnCS_encodeGN_firstRecordDone_exact {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    TM.runConfig (M := GNM)
        (GNM.initialConfig (gnPoint (encodeGN r)))
        (gnFirstRecordDoneSteps r g) =
      gnFirstRecordDoneConfig r g hg := by
  have hbodyLen := gnGateBodyFrames_length_cons g
  have hmid := gnFirstRecordDone_middle_length hg
  have hbodyTail : ∀ frame ∈ gnGateBodyTail g, GNInstallBody frame := by
    intro frame hframe
    refine gnGateBodyFrames_body g frame ?_
    rw [gnGateBodyFrames_cons g]
    exact List.mem_cons_of_mem _ hframe
  have hmiddle : ∀ frame ∈ gnFirstRecordTail r ++ [G1Frame.bof] ++
      ([] : List G1Frame).map gnInstallImage, GNInstallAdmissible frame := by
    intro frame hframe
    simp only [List.map_nil, List.append_nil, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hframe
    rcases hframe with h | rfl
    · exact gnFirstRecordTail_admissible hg frame h
    · exact ⟨by decide, by decide⟩
  have hdriver := gnCS_bodyDriver_recordDone_exact (encodeGN r).length
    (gnLocatePrefix r ++ [G1Frame.cursor]) [] G1Frame.tag (gnGateBodyTail g)
    (gnFirstRecordTail r) [G1Frame.bof] (.carried .cursor) (by trivial)
    (by simp [GNInstallBody]) hbodyTail hmiddle (gnFirstRecordDone_room hg)
  have hsched : gnFirstRecordDoneSteps r g =
      gnBofSeedSteps r +
        gnBodyDriverSteps (G1Frame.tag :: gnGateBodyTail g).length
          (gnBodyRoundMiddle ([] : List G1Frame)
            (gnGateBodyTail g ++ G1Frame.finish :: gnFirstRecordTail r)
            [G1Frame.bof]).length := by
    rw [gnFirstRecordDoneSteps, ← hbodyLen, ← hmid]
  rw [hsched, runConfig_add, gnCS_encodeGN_bofSeed_exact hg,
    gnBofSeed_eq_bodyRoundConfig hg, hdriver]
  apply Configuration.ext_of_components
  · rfl
  · apply Fin.ext
    have hpre := (encodeGNFrames_firstRecord_split hg).2.1
    have hsize := gnRecordSize_eq_body g
    change 4 * ((gnLocatePrefix r ++ [G1Frame.cursor]) ++
        (([] : List G1Frame) ++ G1Frame.tag :: gnGateBodyTail g)).length + 4 =
      4 * (gnRecordsStart r + gnRecordSize (gnGateFields g))
    have hfixed : ((gnLocatePrefix r ++ [G1Frame.cursor]) ++
        (([] : List G1Frame) ++ G1Frame.tag :: gnGateBodyTail g)).length =
        (gnLocatePrefix r).length + 1 + (gnGateBodyFrames g).length := by
      rw [List.nil_append, ← gnGateBodyFrames_cons g]
      simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  · change frameListTape _ = frameListTape _
    rw [gnFirstRecordDone_frames hg]

/-- Complete exact projections of the real-input endpoint.  The first three
conjuncts pin state, head and the full physical tape; the fourth says the
original GN word is restored verbatim; the fifth gives the ordered scratch
image; the sixth identifies that image with the G1 request prefix of the
selected gate; the seventh records the pure semantics of that request at the
actual stage-zero environment, where the current value list is
`gnCurrentValues r [] = r.inputs` and `SLGate.compute` therefore receives
`r.inputs` as the input reader and the empty list of gate results.

The last two conjuncts are statements about the **pure** request determined by
`g`.  Nothing here says the machine has evaluated anything: at this endpoint it
has only relocated the selected record's frames. -/
theorem gnFirstRecordDoneConfig_structure {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    (gnFirstRecordDoneConfig r g hg).state =
        ⟨(0 : Fin 1), GNState.recordDone⟩ ∧
      ((gnFirstRecordDoneConfig r g hg).head : Nat) =
        4 * (gnRecordsStart r + gnRecordSize (gnGateFields g)) ∧
      (gnFirstRecordDoneConfig r g hg).tape =
        frameListTape
          ((encodeGNFrames r ++ (gnRecordFrames .cursor g).map gnInstallImage ++
            [G1Frame.blank]).flatMap G1Frame.bits) ∧
      gnLocatePrefix r ++ G1Frame.cursor :: gnFirstRecordMiddle r =
        encodeGNFrames r ∧
      (gnRecordFrames .cursor g).map gnInstallImage =
        G1Frame.bof :: gnGateBodyFrames g ++ [G1Frame.separator] ∧
      (gnRecordFrames .cursor g).map gnInstallImage ++ r.inputs.map .data =
        g1PrefixFrames (gnFirstRequest r g) ∧
      (gnFirstRequest r g).spec =
        g.compute (fun i => r.inputs[i.val]'(by omega)) [] := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, gnFirstRecord_image_request_prefix r g, ?_⟩
  · simpa [gnFirstRecordMiddle, List.append_assoc] using
      (encodeGNFrames_firstRecord_split hg).1.symm
  · rw [gnRecordFrames_cursor_split g]
    simp [gnGateBodyFrames_map_image, gnInstallImage]
  · have h := (gnWorkRequest_spec (r := r) (prior := []) (g := g) hg).1
    rw [gnCurrentValues_zero] at h
    exact h

/-- Scoped clock fact: the complete proved prefix — validation, locator, the
`firstRecord` door, the cursor seed shuttle and the whole first-record body
driver — fits inside the unchanged public `gnClock`.  This bounds exactly that
prefix.  It is **not** a total installer, multigate, or runtime clock
theorem. -/
theorem gnFirstRecordDoneSteps_le_gnClock {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    gnFirstRecordDoneSteps r g ≤ gnClock (encodeGN r).length := by
  have hlen := gnFirstRecordMiddle_length_split hg
  have hn := gnEncodeGN_length_split hg
  have hseed := gnBofSeedSteps_provenance r
  have hbound : (gnGateBodyFrames g).length ≤ (gnFirstRecordMiddle r).length := by
    omega
  have hprod : (gnGateBodyFrames g).length *
        (8 * (gnFirstRecordMiddle r).length + 30) ≤
      (gnFirstRecordMiddle r).length *
        (8 * (gnFirstRecordMiddle r).length + 30) :=
    Nat.mul_le_mul_right _ hbound
  have hexp : (gnFirstRecordMiddle r).length *
        (8 * (gnFirstRecordMiddle r).length + 30) =
      8 * ((gnFirstRecordMiddle r).length * (gnFirstRecordMiddle r).length) +
        30 * (gnFirstRecordMiddle r).length := by
    rw [Nat.mul_add, Nat.mul_left_comm, Nat.mul_comm (gnFirstRecordMiddle r).length 30]
  have hsq : (gnFirstRecordMiddle r).length * (gnFirstRecordMiddle r).length ≤
      ((encodeGN r).length + 1) * ((encodeGN r).length + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hpow : ((encodeGN r).length + 1) ^ 2 =
      ((encodeGN r).length + 1) * ((encodeGN r).length + 1) := pow_two _
  have hsquare : (encodeGN r).length + 1 ≤
      ((encodeGN r).length + 1) * ((encodeGN r).length + 1) :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hclock : gnClock (encodeGN r).length =
      512 * ((encodeGN r).length + 1) ^ 2 + 512 := rfl
  rw [gnFirstRecordDoneSteps, gnBodyDriverSteps, gnBodyRoundSteps,
    gnBodyTerminalSteps, hclock, hpow]
  rw [hexp] at hprod
  omega

/-! ## One literal real-input record -/

namespace GNBodyDriverProbes

open GNFixedDelegateProbes

/-- Exact literal first-record endpoint for the one-constant-false program: the
original twelve-frame GN word is restored and scratch is exactly
`bof, tag, tag, argSep, argSep, separator` followed by the retained blank. -/
def oneConstFalseRecordDoneConfig : Configuration (M := GNM) 48 where
  state := ⟨(0 : Fin 1), .recordDone⟩
  head := ⟨36, by
    simp [TM.tapeLength, gnCS, gnClock, g1Clock]⟩
  tape := frameListTape
    ([G1Frame.bof, .output false, .separator, .cursor, .tag, .tag,
      .argSep, .argSep, .finish, .separator, .output false, .finish,
      .bof, .tag, .tag, .argSep, .argSep, .separator,
      .blank].flatMap G1Frame.bits)

/-- Kernel-confirmed literal capstone: from the genuine real initial
configuration, 659 rows reach `recordDone` at physical head 36 with the exact
tape above.  This runs every body frame of the record, not just the first. -/
theorem literal_oneConstFalse_recordDone :
    TM.runConfig (M := GNM)
        (GNM.initialConfig (gnPoint (encodeGN oneConstFalseProgram))) 659 =
      oneConstFalseRecordDoneConfig ∧
    (oneConstFalseRecordDoneConfig.head : Nat) = 36 ∧
    oneConstFalseRecordDoneConfig.state =
      ⟨(0 : Fin 1), GNState.recordDone⟩ ∧
    oneConstFalseRecordDoneConfig.tape = frameListTape
      ([G1Frame.bof, .output false, .separator, .cursor, .tag, .tag,
        .argSep, .argSep, .finish, .separator, .output false, .finish,
        .bof, .tag, .tag, .argSep, .argSep, .separator,
        .blank].flatMap G1Frame.bits) := by
  have hg : oneConstFalseProgram.program.gates[0]? =
      some (SLGate.const false : SLGate 0) := by rfl
  have hrun := gnCS_encodeGN_firstRecordDone_exact hg
  have hsched : gnFirstRecordDoneSteps oneConstFalseProgram
      (SLGate.const false : SLGate 0) = 659 := by decide
  rw [hsched] at hrun
  refine ⟨?_, rfl, rfl, rfl⟩
  refine hrun.trans ?_
  apply Configuration.ext_of_components
  · rfl
  · rfl
  · rfl

end GNBodyDriverProbes

end Pnp3.Internal.PsubsetPpoly.TM
