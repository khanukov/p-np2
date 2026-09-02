import Complexity.TMVerifier.TuringToolkit.GateNBoundaryShuttle

/-!
# GN-E2-3a payload-preserving body round and terminal switch (2026-09-02)

**Progress classification: infrastructure, not P-vs-NP mainline progress.**

This slice activates only the payload-preserving installer exit.  A continuing
finite payload dispatches stationarily to an empty source probe; carried
`finish` dispatches stationarily to the fixed `recordDone` state; every other
payload and every non-p0 exit buffer rejects.  One proof-level list invariant
then composes that dispatcher with exactly one existing source-restoring
shuttle.

The resulting ordinary round takes `8*d+30` rows and advances from one source
p0 to the next while restoring the source and appending `gnInstallImage` at the
scratch frontier.  A finish round has the same schedule and one further
stationary row reaches `recordDone`.  This module deliberately has no body-list
driver or induction capstone, no real-initial finish execution, no completed
request record, values/tail work, launch/delegation, commit, loop, total
installer clock, verdict, or acceptance theorem.  E2-3b owns the driver and
real-initial record-done capstone; E2-4 owns continuation from `recordDone`.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

open Pnp3.Internal.PsubsetPpoly.TM.FrameScan
open Encoding

/-! ## Exact finite exit table -/

/-- Exact exit decision: only the finite canonical continuing payloads probe,
finish terminates, every other payload rejects, and non-p0 buffers reject. -/
theorem gnTransition_install_exit_dispatch (phase : Fin 1) (scan : Bool) :
    (∀ aux, GNInstallExitContinue aux →
      gnTransition phase (gnInstallExitState aux) scan =
        (0, .install .probe .p0 .empty, scan, .stay)) ∧
    gnTransition phase (gnInstallExitState (.carried .finish)) scan =
      (0, .recordDone, scan, .stay) ∧
    (∀ aux, GNInstallExitInvalid aux →
      gnTransition phase (gnInstallExitState aux) scan =
        (0, .reject, scan, .stay)) ∧
    (∀ buffer aux, buffer ≠ GNInstallBuffer.p0 →
      gnTransition phase (.install .exit buffer aux) scan =
        (0, .reject, scan, .stay)) := by
  constructor
  · intro aux haux
    cases aux with
    | empty => rfl
    | carried frame =>
        cases frame <;> simp_all [GNInstallExitContinue, gnInstallExitState,
          gnInstallExitDispatch, gnTransition]
  constructor
  · rfl
  constructor
  · intro aux haux
    cases aux with
    | empty => simp [GNInstallExitInvalid, GNInstallExitContinue] at haux
    | carried frame =>
        cases frame <;> simp_all [GNInstallExitInvalid, GNInstallExitContinue,
          gnInstallExitState, gnInstallExitDispatch, gnTransition]
  · intro buffer aux hbuffer
    cases buffer <;> simp_all [gnTransition]

/-! ## Proof-level one-round configuration -/

/-- An ordinary record-body source or the canonical terminal finish. -/
def GNBodyRoundSource (frame : G1Frame) : Prop :=
  GNInstallBody frame ∨ frame = .finish

/-- Frames strictly between the current source and the first scratch blank.
The first part is unprocessed source, while `seed ++ done.map image` is the
already mapped scratch prefix. -/
def gnBodyRoundMiddle (done todo seed : List G1Frame) : List G1Frame :=
  todo ++ seed ++ done.map gnInstallImage

/-- Complete proof-level frame presentation.  The source prefix remains
verbatim, the scratch prefix is mapped, and two blanks pin both the first
frontier and the retained next frontier. -/
def gnBodyRoundFrames (fixed done : List G1Frame) (current : G1Frame)
    (todo seed rest : List G1Frame) : List G1Frame :=
  (fixed ++ done) ++ current ::
    gnBodyRoundMiddle done todo seed ++ .blank :: .blank :: rest

/-- One-round readiness contains only finite-frame/list facts and physical
room.  No natural geometry is stored in `GNState`. -/
structure GNBodyRoundInvariant (n : Nat) (fixed done : List G1Frame)
    (current : G1Frame) (todo seed : List G1Frame)
    (previous : GNInstallAux) : Prop where
  previous_continue : GNInstallExitContinue previous
  source : GNBodyRoundSource current
  middle_admissible :
    ∀ frame ∈ gnBodyRoundMiddle done todo seed, GNInstallAdmissible frame
  room : 4 * ((fixed ++ done).length +
      (gnBodyRoundMiddle done todo seed).length + 2) < GNM.tapeLength n

/-- Dormant payload-preserving exit at the current source p0. -/
def gnBodyRoundConfig (n : Nat) (fixed done : List G1Frame)
    (current : G1Frame) (todo seed rest : List G1Frame)
    (previous : GNInstallAux)
    (hroom : 4 * ((fixed ++ done).length +
      (gnBodyRoundMiddle done todo seed).length + 2) < GNM.tapeLength n) :
    Configuration (M := GNM) n :=
  gnCopyShuttle.cfg n (4 * (fixed ++ done).length) (by
      change 4 * (fixed ++ done).length < GNM.tapeLength n
      omega)
    (frameListTape
      ((gnBodyRoundFrames fixed done current todo seed rest).flatMap
        G1Frame.bits))
    (gnInstallExitState previous)

/-- The definition pins the exact state, head, restored source/mapped-scratch
list presentation, and first/retained blank frontier. -/
theorem gnBodyRoundConfig_structure (n : Nat) (fixed done : List G1Frame)
    (current : G1Frame) (todo seed rest : List G1Frame)
    (previous : GNInstallAux)
    (hroom : 4 * ((fixed ++ done).length +
      (gnBodyRoundMiddle done todo seed).length + 2) < GNM.tapeLength n) :
    (gnBodyRoundConfig n fixed done current todo seed rest previous hroom).state =
        ⟨(0 : Fin 1), gnInstallExitState previous⟩ ∧
      ((gnBodyRoundConfig n fixed done current todo seed rest previous hroom).head :
        Nat) = 4 * (fixed ++ done).length ∧
      (gnBodyRoundConfig n fixed done current todo seed rest previous hroom).tape =
        frameListTape
          ((gnBodyRoundFrames fixed done current todo seed rest).flatMap
            G1Frame.bits) := by
  exact ⟨rfl, rfl, rfl⟩

/-- Dispatcher plus shuttle schedule. -/
def gnBodyRoundSteps (distance : Nat) : Nat := 8 * distance + 30

/-- Finish round followed by the stationary terminal switch. -/
def gnBodyTerminalSteps (distance : Nat) : Nat := 8 * distance + 31

/-- Exact arithmetic provenance for both exposed per-round schedules. -/
theorem gnBodyRoundSteps_provenance (distance : Nat) :
    gnBodyRoundSteps distance = 1 + (8 * distance + 29) ∧
      gnBodyTerminalSteps distance = gnBodyRoundSteps distance + 1 := by
  simp [gnBodyRoundSteps, gnBodyTerminalSteps]
  omega

/-- Moving one source frame from `todo` to `done` leaves the shuttle middle
distance constant because its image is appended to the scratch prefix. -/
theorem gnBodyRoundMiddle_length_constant (done later seed : List G1Frame)
    (current next : G1Frame) :
    (gnBodyRoundMiddle done (next :: later) seed).length =
      (gnBodyRoundMiddle (done ++ [current]) later seed).length := by
  simp [gnBodyRoundMiddle]
  omega

private theorem gnCS_bodyExit_to_probe_one (n : Nat)
    (fixed done : List G1Frame) (current : G1Frame)
    (todo seed rest : List G1Frame) (previous : GNInstallAux)
    (hroom : 4 * ((fixed ++ done).length +
      (gnBodyRoundMiddle done todo seed).length + 2) < GNM.tapeLength n)
    (hprevious : GNInstallExitContinue previous) :
    TM.runConfig (M := GNM)
        (gnBodyRoundConfig n fixed done current todo seed rest previous hroom) 1 =
      gnCopyShuttle.cfg n (4 * (fixed ++ done).length) (by
          change 4 * (fixed ++ done).length < GNM.tapeLength n
          omega)
        (frameListTape
          ((gnBodyRoundFrames fixed done current todo seed rest).flatMap
            G1Frame.bits))
        (.install .probe .p0 .empty) := by
  let head := 4 * (fixed ++ done).length
  let tape : Fin (GNM.tapeLength n) → Bool := frameListTape
    ((gnBodyRoundFrames fixed done current todo seed rest).flatMap G1Frame.bits)
  have hhead : head < GNM.tapeLength n := by
    apply lt_trans (b := 4 * ((fixed ++ done).length +
      (gnBodyRoundMiddle done todo seed).length + 2))
    · dsimp [head]
      omega
    · exact hroom
  have hhead' : head < (Phased.machine gnCS).tapeLength n := by
    simpa only using hhead
  have hstep := Phased.stepStay gnCS gnCS.startPhase n head hhead' tape
    (gnInstallExitState previous) (.install .probe .p0 .empty)
    (tape ⟨head, hhead⟩)
    ((gnTransition_install_exit_dispatch gnCS.startPhase _).1 previous hprevious)
  rw [writeCell_self] at hstep
  rw [runConfig_one]
  simpa [gnBodyRoundConfig, head, tape] using hstep

/-! ## Exact ordinary and terminal rounds -/

/-- One exact nonterminal round: the exit dispatcher takes one stationary row,
the shuttle takes `8*d+29`, the source is restored, `gnInstallImage current`
is appended at the first blank, and the head advances four cells into an exit
carrying the current source. -/
theorem gnCS_bodyRound_exact (n : Nat) (fixed done : List G1Frame)
    (current : G1Frame) (todo seed rest : List G1Frame)
    (previous : GNInstallAux)
    (hinv : GNBodyRoundInvariant n fixed done current todo seed previous)
    (hbody : GNInstallBody current) :
    TM.runConfig (M := GNM)
        (gnBodyRoundConfig n fixed done current todo seed rest previous hinv.room)
        (gnBodyRoundSteps (gnBodyRoundMiddle done todo seed).length) =
      gnCopyShuttle.cfg n (4 * (fixed ++ done).length + 4) (by
          change 4 * (fixed ++ done).length + 4 < GNM.tapeLength n
          have h := hinv.room
          omega)
        (frameListTape
          (((fixed ++ done) ++ current ::
            gnBodyRoundMiddle done todo seed ++
              gnInstallImage current :: .blank :: rest).flatMap G1Frame.bits))
        (gnInstallExitState (.carried current)) := by
  have hsource : current ≠ G1Frame.blank ∧ current ≠ .output true := by
    rcases hbody with rfl | rfl | rfl <;> decide
  have hshuttle := gnCS_copyShuttle_nextBlank n (fixed ++ done) current
    (gnBodyRoundMiddle done todo seed) rest .empty hsource
    (by
      intro frame hframe
      exact hinv.middle_admissible frame hframe)
    hinv.room
  rw [gnBodyRoundSteps, show 8 * (gnBodyRoundMiddle done todo seed).length + 30 =
      1 + (8 * (gnBodyRoundMiddle done todo seed).length + 29) by omega,
    runConfig_add, gnCS_bodyExit_to_probe_one n fixed done current todo seed rest
      previous hinv.room hinv.previous_continue]
  simpa [gnBodyRoundFrames] using hshuttle

/-- E2-3b iteration endpoint.  When another source exists, one ordinary round
is exactly the next proof-level round configuration.  The caller supplies the
next room proof; no list driver or induction is proved here. -/
theorem gnCS_bodyRound_iteration_exact (n : Nat) (fixed done : List G1Frame)
    (current next : G1Frame) (later seed : List G1Frame)
    (previous : GNInstallAux)
    (hinv : GNBodyRoundInvariant n fixed done current (next :: later) seed
      previous)
    (hbody : GNInstallBody current)
    (hnextRoom : 4 * ((fixed ++ (done ++ [current])).length +
      (gnBodyRoundMiddle (done ++ [current]) later seed).length + 2) <
        GNM.tapeLength n) :
    TM.runConfig (M := GNM)
        (gnBodyRoundConfig n fixed done current (next :: later) seed []
          previous hinv.room)
        (gnBodyRoundSteps
          (gnBodyRoundMiddle done (next :: later) seed).length) =
      gnBodyRoundConfig n fixed (done ++ [current]) next later seed []
        (.carried current) hnextRoom := by
  rw [gnCS_bodyRound_exact n fixed done current (next :: later) seed []
    previous hinv hbody]
  apply Configuration.ext_of_components
  · rfl
  · apply Fin.ext
    change 4 * (fixed ++ done).length + 4 =
      4 * (fixed ++ (done ++ [current])).length
    simp
    omega
  · simpa [gnBodyRoundConfig, gnBodyRoundFrames, gnBodyRoundMiddle,
      List.map_append, List.append_assoc, g1FrameCodec_bits] using
      (frameListTape_append_blank (L := GNM.tapeLength n) g1FrameCodec
        ((fixed ++ done) ++ current :: next :: later ++ seed ++
          done.map gnInstallImage ++ [gnInstallImage current, .blank])
        G1Frame.blank rfl)

/-- A terminal finish source executes the same payload-preserving shuttle
round, restoring finish and installing separator, before any decision occurs. -/
theorem gnCS_bodyFinishRound_exact (n : Nat) (fixed done : List G1Frame)
    (todo seed rest : List G1Frame) (previous : GNInstallAux)
    (hinv : GNBodyRoundInvariant n fixed done .finish todo seed previous) :
    TM.runConfig (M := GNM)
        (gnBodyRoundConfig n fixed done .finish todo seed rest previous hinv.room)
        (gnBodyRoundSteps (gnBodyRoundMiddle done todo seed).length) =
      gnCopyShuttle.cfg n (4 * (fixed ++ done).length + 4) (by
          change 4 * (fixed ++ done).length + 4 < GNM.tapeLength n
          have h := hinv.room
          omega)
        (frameListTape
          (((fixed ++ done) ++ G1Frame.finish ::
            gnBodyRoundMiddle done todo seed ++
              G1Frame.separator :: .blank :: rest).flatMap G1Frame.bits))
        (gnInstallExitState (.carried .finish)) := by
  have hshuttle := gnCS_copyShuttle_nextBlank n (fixed ++ done) .finish
    (gnBodyRoundMiddle done todo seed) rest .empty (by decide)
    (by
      intro frame hframe
      exact hinv.middle_admissible frame hframe)
    hinv.room
  rw [gnBodyRoundSteps, show 8 * (gnBodyRoundMiddle done todo seed).length + 30 =
      1 + (8 * (gnBodyRoundMiddle done todo seed).length + 29) by omega,
    runConfig_add, gnCS_bodyExit_to_probe_one n fixed done .finish todo seed rest
      previous hinv.room hinv.previous_continue]
  simpa [gnBodyRoundFrames, gnInstallImage] using hshuttle

/-- Exact one-row terminal switch from carried finish at arbitrary proof-level
head/tape.  No public stability theorem for `recordDone` is exposed. -/
theorem gnCS_finishExit_to_recordDone_one (n head : Nat)
    (hhead : head < GNM.tapeLength n)
    (tape : Fin (GNM.tapeLength n) → Bool) :
    TM.runConfig (M := GNM)
        (gnCopyShuttle.cfg n head hhead tape
          (gnInstallExitState (.carried .finish))) 1 =
      gnCopyShuttle.cfg n head hhead tape .recordDone := by
  have hstep := Phased.stepStay gnCS gnCS.startPhase n head hhead tape
    (gnInstallExitState (.carried .finish)) .recordDone (tape ⟨head, hhead⟩)
    (gnTransition_install_exit_dispatch gnCS.startPhase _).2.1
  rw [writeCell_self] at hstep
  rw [runConfig_one]
  simpa using hstep

/-- Terminal round plus the separate stationary switch, exactly `8*d+31`.
The endpoint is only fixed `recordDone`; continuation belongs to E2-4. -/
theorem gnCS_bodyFinishRound_recordDone_exact (n : Nat)
    (fixed done : List G1Frame) (todo seed rest : List G1Frame)
    (previous : GNInstallAux)
    (hinv : GNBodyRoundInvariant n fixed done .finish todo seed previous) :
    TM.runConfig (M := GNM)
        (gnBodyRoundConfig n fixed done .finish todo seed rest previous hinv.room)
        (gnBodyTerminalSteps (gnBodyRoundMiddle done todo seed).length) =
      gnCopyShuttle.cfg n (4 * (fixed ++ done).length + 4) (by
          change 4 * (fixed ++ done).length + 4 < GNM.tapeLength n
          have h := hinv.room
          omega)
        (frameListTape
          (((fixed ++ done) ++ G1Frame.finish ::
            gnBodyRoundMiddle done todo seed ++
              G1Frame.separator :: .blank :: rest).flatMap G1Frame.bits))
        .recordDone := by
  rw [gnBodyTerminalSteps, show 8 * (gnBodyRoundMiddle done todo seed).length +
      31 = gnBodyRoundSteps (gnBodyRoundMiddle done todo seed).length + 1 by
        simp [gnBodyRoundSteps],
    runConfig_add, gnCS_bodyFinishRound_exact n fixed done todo seed rest
      previous hinv,
    gnCS_finishExit_to_recordDone_one]

/-! ## Exit-boundary rejection and scoped clock -/

/-- Invalid carried payloads reject in exactly one stationary exit row. -/
theorem gnCS_install_exit_invalid_reject_one (n head : Nat)
    (hhead : head < GNM.tapeLength n)
    (tape : Fin (GNM.tapeLength n) → Bool) (aux : GNInstallAux)
    (hinvalid : GNInstallExitInvalid aux) :
    TM.runConfig (M := GNM)
        (gnCopyShuttle.cfg n head hhead tape (gnInstallExitState aux)) 1 =
      gnCopyShuttle.cfg n head hhead tape .reject := by
  have hstep := Phased.stepStay gnCS gnCS.startPhase n head hhead tape
    (gnInstallExitState aux) .reject (tape ⟨head, hhead⟩)
    ((gnTransition_install_exit_dispatch gnCS.startPhase _).2.2.1 aux hinvalid)
  rw [writeCell_self] at hstep
  rw [runConfig_one]
  simpa using hstep

/-- Every non-p0 exit buffer rejects in exactly one stationary row. -/
theorem gnCS_install_exit_badBuffer_reject_one (n head : Nat)
    (hhead : head < GNM.tapeLength n)
    (tape : Fin (GNM.tapeLength n) → Bool) (buffer : GNInstallBuffer)
    (aux : GNInstallAux) (hbuffer : buffer ≠ .p0) :
    TM.runConfig (M := GNM)
        (gnCopyShuttle.cfg n head hhead tape (.install .exit buffer aux)) 1 =
      gnCopyShuttle.cfg n head hhead tape .reject := by
  have hstep := Phased.stepStay gnCS gnCS.startPhase n head hhead tape
    (.install .exit buffer aux) .reject (tape ⟨head, hhead⟩)
    ((gnTransition_install_exit_dispatch gnCS.startPhase _).2.2.2 buffer aux
      hbuffer)
  rw [writeCell_self] at hstep
  rw [runConfig_one]
  simpa using hstep

/-- Reserved `1101` after any valid continuing exit dispatch rejects in exactly
five rows: one stationary dispatch and four physical probe rows. -/
theorem gnCS_install_exit_reserved1101_reject_five (n base : Nat)
    (hsafe : base + 4 < GNM.tapeLength n)
    (tape : Fin (GNM.tapeLength n) → Bool)
    (hbits : physicalBitsAt hsafe tape = [true, true, false, true])
    (aux : GNInstallAux) (haux : GNInstallExitContinue aux) :
    TM.runConfig (M := GNM)
        (Phased.alignedAt gnCS gnCS.startPhase n base (by
          change base < GNM.tapeLength n
          omega) tape
          (gnInstallExitState aux)) 5 =
      Phased.alignedAt gnCS gnCS.startPhase n (base + 3) (by
        change base + 3 < GNM.tapeLength n
        omega) tape
        .reject := by
  have hexit := Phased.stepStay gnCS gnCS.startPhase n base (by
      change base < GNM.tapeLength n
      omega) tape
    (gnInstallExitState aux) (.install .probe .p0 .empty)
    (tape ⟨base, by omega⟩)
    ((gnTransition_install_exit_dispatch gnCS.startPhase _).1 aux haux)
  rw [writeCell_self] at hexit
  have hfirst := gnCS_firstRecord_reserved1101_reject_five n base hsafe tape hbits
  rw [show 5 = 1 + 4 by omega, runConfig_add, runConfig_one] at hfirst ⊢
  have hdoor := Phased.stepStay gnCS gnCS.startPhase n base (by
      change base < GNM.tapeLength n
      omega) tape
    .firstRecord (.install .probe .p0 .empty) (tape ⟨base, by omega⟩)
    (gnTransition_boundary_rows gnCS.startPhase _).1
  rw [writeCell_self] at hdoor
  have hdoor' : GNM.stepConfig
      (Phased.alignedAt gnCS gnCS.startPhase n base (by
        change base < GNM.tapeLength n
        omega) tape .firstRecord) =
      Phased.alignedAt gnCS gnCS.startPhase n base (by
        change base < GNM.tapeLength n
        omega) tape (.install .probe .p0 .empty) := by
    simpa using hdoor
  rw [hexit]
  rw [hdoor'] at hfirst
  exact hfirst

/-- Stable reject padding after the exact five-row exit/probe failure. -/
theorem gnCS_install_exit_reserved1101_reject_stable (n base : Nat)
    (hsafe : base + 4 < GNM.tapeLength n)
    (tape : Fin (GNM.tapeLength n) → Bool)
    (hbits : physicalBitsAt hsafe tape = [true, true, false, true])
    (aux : GNInstallAux) (haux : GNInstallExitContinue aux) (k : Nat) :
    TM.runConfig (M := GNM)
        (Phased.alignedAt gnCS gnCS.startPhase n base (by
          change base < GNM.tapeLength n
          omega) tape
          (gnInstallExitState aux)) (5 + k) =
      Phased.alignedAt gnCS gnCS.startPhase n (base + 3) (by
        change base + 3 < GNM.tapeLength n
        omega) tape
        .reject := by
  rw [runConfig_add,
    gnCS_install_exit_reserved1101_reject_five n base hsafe tape hbits aux haux]
  exact gnCS_reject_stable _ rfl k

/-- Per-round clock bound only.  A caller-supplied source/frontier span inside
the original input length bounds one terminal-sized round; this is not a total
body/install clock theorem. -/
theorem gnBodyTerminalSteps_le_gnClock {n distance : Nat}
    (hspan : 4 * (distance + 2) ≤ n) :
    gnBodyTerminalSteps distance ≤ gnClock n := by
  have hsquare : n + 1 ≤ (n + 1) ^ 2 := by
    rw [pow_two]
    exact Nat.le_mul_of_pos_left _ (by omega)
  unfold gnBodyTerminalSteps gnClock g1Clock
  omega

/-! ## One ordinary literal round -/

namespace GNBodyRoundProbes

open GNFixedDelegateProbes

/-- Exact first-body endpoint for the one-constant-false seed.  The original
12-frame GN word is restored and scratch is exactly `bof, tag, blank`. -/
def oneConstFalseTagConfig : Configuration (M := GNM) 48 where
  state := ⟨(0 : Fin 1), gnInstallExitState (.carried .tag)⟩
  head := ⟨20, by
    simp [TM.tapeLength, gnCS, gnClock, g1Clock]⟩
  tape := frameListTape
    ([G1Frame.bof, .output false, .separator, .cursor, .tag, .tag,
      .argSep, .argSep, .finish, .separator, .output false, .finish,
      .bof, .tag, .blank].flatMap G1Frame.bits)

/-- From the live E2-2 bof seed, one dispatcher row plus one tag shuttle takes
exactly 94 rows, advances head 16 to 20, and leaves carried tag at exit. -/
theorem literal_oneConstFalse_tagRound :
    TM.runConfig (M := GNM)
        (gnBofSeedConfig oneConstFalseProgram
          (SLGate.const false : SLGate 0) (by rfl)) 94 =
      oneConstFalseTagConfig ∧
    (oneConstFalseTagConfig.head : Nat) = 20 ∧
    oneConstFalseTagConfig.state =
      ⟨(0 : Fin 1), gnInstallExitState (.carried .tag)⟩ ∧
    oneConstFalseTagConfig.tape = frameListTape
      ([G1Frame.bof, .output false, .separator, .cursor, .tag, .tag,
        .argSep, .argSep, .finish, .separator, .output false, .finish,
        .bof, .tag, .blank].flatMap G1Frame.bits) := by
  let fixed : List G1Frame :=
    gnLocatePrefix oneConstFalseProgram ++ [.cursor]
  let todo : List G1Frame := (gnFirstRecordMiddle oneConstFalseProgram).drop 1
  let seed : List G1Frame := [.bof]
  have hinv : GNBodyRoundInvariant 48 fixed [] .tag todo seed
      (.carried .cursor) := by
    refine ⟨by trivial, by simp [GNBodyRoundSource, GNInstallBody], ?_, ?_⟩
    · intro frame hframe
      simp [gnBodyRoundMiddle, todo, seed, oneConstFalseProgram,
        gnFirstRecordMiddle, gnFirstRecordInner, gnRecordsFrames,
        gnFieldRecordsFrames, g1RecordFrames, gnGateFields, G1Tag.units,
        GNInstallAdmissible] at hframe ⊢
      rcases hframe with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide
    · change 4 * ((fixed ++ []).length +
          (gnBodyRoundMiddle [] todo seed).length + 2) < GNM.tapeLength 48
      simp [fixed, todo, seed, gnBodyRoundMiddle, gnLocatePrefix,
        gnFirstRecordMiddle,
        gnFirstRecordInner, gnRecordsFrames, gnFieldRecordsFrames,
        g1RecordFrames, gnGateFields, G1Tag.units, oneConstFalseProgram,
        TM.tapeLength, gnCS, gnClock, g1Clock]
  have hstart :
      gnBofSeedConfig oneConstFalseProgram
          (SLGate.const false : SLGate 0) (by rfl) =
        gnBodyRoundConfig 48 fixed [] .tag todo seed [] (.carried .cursor)
          hinv.room := by
    apply Configuration.ext_of_components
    · rfl
    · rfl
    · simpa [gnBofSeedConfig, gnBodyRoundConfig, gnBodyRoundFrames,
        gnBodyRoundMiddle, fixed, todo, seed, gnLocatePrefix,
        gnFirstRecordMiddle, gnFirstRecordInner, gnRecordsFrames,
        gnFieldRecordsFrames, g1RecordFrames, gnGateFields, G1Tag.units,
        oneConstFalseProgram, g1FrameCodec_bits, List.append_assoc] using
        (frameListTape_append_blank (L := GNM.tapeLength 48) g1FrameCodec
          [G1Frame.bof, .output false, .separator, .cursor, .tag, .tag,
            .argSep, .argSep, .finish, .separator, .output false, .finish,
            .bof, .blank]
          G1Frame.blank rfl)
  have hrun := gnCS_bodyRound_exact 48 fixed [] .tag todo seed []
    (.carried .cursor) hinv (by simp [GNInstallBody])
  have hschedule : gnBodyRoundSteps (gnBodyRoundMiddle [] todo seed).length =
      94 := by
    decide
  rw [hschedule] at hrun
  rw [hstart]
  refine ⟨?_, rfl, rfl, rfl⟩
  exact hrun.trans (by
    apply Configuration.ext_of_components
    · rfl
    · rfl
    · rfl)

end GNBodyRoundProbes

end Pnp3.Internal.PsubsetPpoly.TM
