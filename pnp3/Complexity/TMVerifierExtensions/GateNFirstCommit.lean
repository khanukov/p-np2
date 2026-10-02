import Complexity.TMVerifierExtensions.GateNFirstCommitKernel
import Complexity.TMVerifierExtensions.GateNFirstRequestLaunch

/-! GN-E2-5e infrastructure: canonical first-return commit, with retained scratch.
No iteration, acceptance, clock adequacy, or lower-bound source reduction. -/
namespace Pnp3.Internal.PsubsetPpoly.TM
open FrameScan Encoding
set_option maxHeartbeats 2000000
namespace GNCommitProof

theorem Path.replicate (res : Bool) (m : GNCommitMode) (f : G1Frame)
    (hm : ¬ (m = .seekCursor ∨ m = .seekOpening))
    (hd : gnCommitAdvance m f res = (.commitRead m .p0 res, .right)) (k : Nat) :
    Path res m (List.replicate k f) m := by
  induction k with
  | zero => exact .nil _
  | succ k ih => exact .cons hm hd ih

theorem Path.inputs (res : Bool) (bs : List Bool) :
    Path res .inputs (bs.map .data) .inputs := by
  induction bs with
  | nil => exact .nil _
  | cons b bs ih => exact .cons (by simp) rfl ih

def recordBody (f : GNField) : List G1Frame :=
  List.replicate f.1.units .tag ++ [.argSep] ++ List.replicate f.2.1 .index ++
    [.argSep] ++ List.replicate f.2.2 .index ++ [.finish]

theorem Path.record (res : Bool) (f : GNField) :
    Path res .tag0 (recordBody f) .boundary := by
  have ht : ∀ tag : G1Tag, Path res .tag0 (List.replicate tag.units .tag ++ [.argSep]) .arg1 := by
    intro tag
    cases tag <;> (repeat first | apply Path.cons (by simp) rfl | exact Path.nil _)
  simpa only [recordBody, List.append_assoc] using ((ht f.1).append ((Path.replicate res .arg1 .index (by simp) rfl f.2.1).append
    ((Path.cons (f := .argSep) (by simp) rfl (Path.nil .arg2)).append
      ((Path.replicate res .arg2 .index (by simp) rfl f.2.2).append
        (Path.cons (f := .finish) (by simp) rfl (Path.nil .boundary))))))

def edge (terminal : Bool) (res : Bool) (tail : List G1Frame) : List G1Frame :=
  if terminal then .separator :: .output res :: tail else .cursor :: tail

def oldEdge (terminal : Bool) (tail : List G1Frame) : List G1Frame :=
  if terminal then .separator :: .output false :: tail else .bof :: tail

theorem branch (n : Nat) (pre tail : List G1Frame) (terminal res : Bool)
    (hr : 4*pre.length+8 < GNM.tapeLength n) :
    TM.runConfig (M := GNM)
      (gnCommitConfig n (4*pre.length) (by omega)
        (frameListTape ((pre ++ oldEdge terminal tail).flatMap G1Frame.bits))
        (.commitRead .boundary .p0 res)) 15 =
      gnCommitConfig n (4*pre.length+(if terminal then 8 else 0)) (by split <;> omega)
        (frameListTape ((pre ++ edge terminal res tail).flatMap G1Frame.bits))
        (if terminal then .firstCommitTerminal else .firstCommitNext) := by
  cases terminal
  · have hp := patch n pre tail .bof .boundary .cursor res (by simp) rfl (by omega)
    have hw := Phased.holdWalk4 gnCS gnCS.startPhase n (4*pre.length) (by change 4*pre.length+4 < GNM.tapeLength n; omega)
      (frameListTape ((pre ++ G1Frame.cursor :: tail).flatMap G1Frame.bits))
      (.commitNextBack (.p3 false false false)) (.commitNextBack (.p2 false false))
      (.commitNextBack (.p1 false)) (.commitNextBack .p0) .firstCommitNext
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    change TM.runConfig (M := GNM) _ (11+4) = _
    simp only [oldEdge, Bool.false_eq_true, ↓reduceIte]
    rw [runConfig_add, hp]
    simpa only [gnCommitTarget, gnCommitWriteExit, edge, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] using hw
  · have hs := read n (4*pre.length) (by omega) _ .boundary res (by simp) .separator
      (.commitRead .terminalOutput .p0 res) true rfl
      (physicalBitsAt_flatMap g1FrameCodec pre (.output false :: tail) .separator (by omega))
    have hp := patch n (pre ++ [.separator]) tail (.output false) .terminalOutput .output res
      (by simp) rfl (by simp only [List.length_append, List.length_singleton]; omega)
    change TM.runConfig (M := GNM) _ (4+11) = _
    rw [runConfig_add]
    simp only [oldEdge, ite_true, g1FrameCodec_bits] at hs ⊢
    rw [hs]
    simp only [show 4*pre.length+3+1 = 4*pre.length+4 by omega]
    simpa [List.append_assoc, Nat.mul_add, Nat.add_assoc, edge, gnCommitTarget,
      gnCommitWriteExit] using hp

set_option cleanup.letToHave false in
/-- Pure list geometry of the full pass. These premises are discharged from
concrete encodings below; the public returned capstone takes only hg and res. -/
theorem core (n : Nat) (inputs : List Bool) (k : Nat) (f : GNField)
    (tail post : List G1Frame) (terminal res : Bool)
    (hb : ∀ x ∈ recordBody f ++ oldEdge terminal tail, revAdvance false .scan x = .scan)
    (hr : 4*((G1Frame.bof :: inputs.map .data).length + k + 3 +
      (recordBody f).length + (oldEdge terminal tail).length) < GNM.tapeLength n)
    (hedge : 2 ≤ (oldEdge terminal tail).length) :
    let a := G1Frame.bof :: inputs.map G1Frame.data
    let slots := List.replicate k (G1Frame.output false) ++ [G1Frame.separator]
    let fs := a ++ .output false :: slots ++ .cursor :: recordBody f ++ oldEdge terminal tail
    TM.runConfig (M := GNM)
      (gnCommitConfig n (4*fs.length-1) (by
        simp only [fs, a, slots, List.length_append, List.length_cons, List.length_replicate,
          List.length_nil, List.length_map] at *
        omega)
        (frameListTape ((fs ++ post).flatMap G1Frame.bits)) (gnReturnedState res))
      (4*fs.length + 4*inputs.length + 4*(k+1) + 4*((recordBody f).length+1) + 39) =
    gnCommitConfig n (4*(a.length+1+slots.length+1+(recordBody f).length) +
        (if terminal then 8 else 0)) (by
          simp only [a, slots, List.length_append, List.length_replicate, List.length_cons,
            List.length_nil, List.length_map] at *
          split <;> omega)
      (frameListTape ((a ++ .data res :: slots ++ .spent :: recordBody f ++
        edge terminal res tail ++ post).flatMap G1Frame.bits))
      (if terminal then .firstCommitTerminal else .firstCommitNext) := by
  dsimp only
  let a := G1Frame.bof :: inputs.map G1Frame.data
  let slots := List.replicate k (G1Frame.output false) ++ [G1Frame.separator]
  let suffix := recordBody f ++ oldEdge terminal tail ++ post
  let t := frameListTape (L := GNM.tapeLength n)
    ((a ++ .output false :: slots ++ .cursor :: recordBody f ++ oldEdge terminal tail ++ post).flatMap G1Frame.bits)
  have ha : a.length = inputs.length+1 := by simp [a]
  have hslots : slots.length = k+1 := by simp [slots]
  have room : 4*(a.length + k + 3 + (recordBody f).length +
      (oldEdge terminal tail).length) < GNM.tapeLength n := hr
  have hlen : (a ++ .output false :: slots ++ .cursor :: recordBody f ++ oldEdge terminal tail).length =
      a.length+slots.length+(recordBody f).length+(oldEdge terminal tail).length+2 := by simp; omega
  have he : ∀ h hh, TM.runConfig (M := GNM) (gnCommitConfig n h hh t (gnReturnedState res)) 1 =
      gnCommitConfig n h hh t (.commitRead .seekCursor .r3 res) := by
    intro h hh
    rw [runConfig_one]
    exact stay n h hh t _ _ (by cases res <;> rfl)
  have hseek := reverse_exact n (a ++ .output false :: slots) (recordBody f ++ oldEdge terminal tail)
    post false res hb (by simp only [List.length_append, List.length_cons] at *; dsimp [a, slots] at *; omega)
  have htransfer : ∀ hh, TM.runConfig (M := GNM)
      (gnCommitConfig n (4*(a.length+1+slots.length)) hh t (.commitTransfer res)) 1 =
      gnCommitConfig n (4*(a.length+1+slots.length)-1) (by omega) t
        (.commitRead .seekOpening .r3 res) := by
    intro hh
    rw [runConfig_one]
    exact Phased.holdLeft gnCS gnCS.startPhase n _ hh (by omega) t _ _ (fun _ => rfl)
  have hopen := reverse_exact n [] (inputs.map .data ++ .output false :: slots)
    (.cursor :: suffix) true res (by
      intro x hx
      simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.mem_map,
        slots, List.mem_replicate, List.not_mem_nil, or_false] at hx
      rcases hx with ⟨b, _, rfl⟩ | rfl | ⟨_, rfl⟩ | rfl <;> rfl)
    (by simp only [List.length_nil, List.length_append, List.length_cons, List.length_map]; omega)
  have hinput := (Path.cons (m := .opening) (f := .bof) (by simp) rfl (Path.inputs res inputs)).scan n []
    (.output false :: slots ++ .cursor :: suffix) (by simp only [List.length_nil, List.length_cons, List.length_map]; omega)
  have hslot := patch n a (slots ++ .cursor :: suffix) (.output false) .inputs .slot res
    (by simp) rfl (by omega)
  have hslotpath : Path res .slots slots .cursor :=
    (Path.replicate res .slots (.output false) (by simp) rfl k).append
      (Path.cons (f := .separator) (by simp) rfl (Path.nil .cursor))
  have hslotscan := hslotpath.scan n (a ++ [.data res]) (.cursor :: suffix)
    (by simp only [List.length_append, List.length_singleton]; omega)
  have hcursor := patch n (a ++ .data res :: slots) suffix .cursor .cursor .spent res
    (by simp) rfl (by simp only [List.length_append, List.length_cons]; omega)
  have hbody := (Path.record res f).scan n (a ++ .data res :: slots ++ [.spent])
    (oldEdge terminal tail ++ post) (by
      simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil]
      omega)
  have hbranch := branch n (a ++ .data res :: slots ++ .spent :: recordBody f) (tail ++ post)
    terminal res (by simp only [List.length_append, List.length_cons]; omega)
  have hepost : edge terminal res (tail ++ post) = edge terminal res tail ++ post := by
    cases terminal <;> rfl
  have hopost : oldEdge terminal (tail ++ post) = oldEdge terminal tail ++ post := by
    cases terminal <;> rfl
  simp only [hepost, hopost] at hbranch
  -- Normalize the shared full tapes and frame positions once, before composing.
  simp only [revAnchor, revMode, revExit, Bool.false_eq_true, ite_true,
    ↓reduceIte, List.length_append, List.length_cons, List.length_nil, List.length_map,
    List.length_singleton, List.nil_append, List.cons_append, List.append_assoc,
    Nat.zero_add, Nat.add_zero, gnCommitWriteExit, gnCommitTarget] at hseek hopen hinput hslot hslotscan hcursor hbody hbranch
  -- The concrete nine macrosteps contain every physical reposition row.
  have htime : 4*(a.length+slots.length+(recordBody f).length+(oldEdge terminal tail).length+2) +
      4*inputs.length + 4*(k+1) + 4*((recordBody f).length+1) + 39 =
      1 + (4*(recordBody f ++ oldEdge terminal tail).length+4) + 1 +
      (4*(inputs.map G1Frame.data ++ .output false :: slots).length+4) +
      4*a.length + 11 + 4*slots.length + 11 + 4*(recordBody f).length + 15 := by
    simp only [List.length_append, List.length_cons, List.length_map]
    omega
  have hclock : 4*(a ++ .output false :: slots ++ .cursor :: recordBody f ++ oldEdge terminal tail).length +
      4*inputs.length + 4*(k+1) + 4*((recordBody f).length+1) + 39 =
      1 + ((4*(recordBody f ++ oldEdge terminal tail).length+4) + (1 +
      ((4*(inputs.map G1Frame.data ++ .output false :: slots).length+4) +
      (4*a.length + (11 + (4*slots.length + (11 + (4*(recordBody f).length + 15)))))))) := by
    rw [hlen]; omega
  rw [hclock, runConfig_add, he, runConfig_add]
  have hstart : 4*(a ++ .output false :: slots ++ .cursor :: recordBody f ++ oldEdge terminal tail).length-1 =
      4*(a.length+(slots.length+1)+((recordBody f).length+(oldEdge terminal tail).length))+3 := by
    rw [hlen]; omega
  dsimp only [a, slots] at hstart
  simp only [hstart]
  simp only [a, slots, t, List.append_assoc, List.cons_append, List.length_append,
    List.length_cons, List.length_map, List.length_replicate, List.length_nil] at hseek ⊢
  rw [hseek, runConfig_add]
  -- Normalize geometry without splitting any macrostep's clock.
  simp only [a, slots, suffix, t, List.append_assoc, List.cons_append,
    List.length_append, List.length_cons, List.length_map, List.length_nil,
    List.length_replicate, List.nil_append, Nat.add_zero, Nat.zero_add] at *
  have htpos : inputs.length+1+(k+1+1) = inputs.length+1+1+(k+1) := by omega
  simp only [htpos]
  rw [htransfer (by omega), runConfig_add]
  have hopos : 4*(inputs.length+1+1+(k+1))-1 = 4*(inputs.length+(k+1+1))+3 := by omega
  simp only [hopos]
  rw [hopen, runConfig_add, hinput, runConfig_add, hslot, runConfig_add]
  simp only [show 4*(inputs.length+1)+4 = 4*(inputs.length+1+1) by omega]
  rw [hslotscan, runConfig_add]
  simp only [← htpos]
  rw [hcursor, runConfig_add]
  simp only [show 4*(inputs.length+1+(k+1+1))+4 =
    4*(inputs.length+1+(k+1+1)+1) by omega]
  simp only [Nat.add_assoc] at hbody ⊢
  rw [hbody]
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hbranch

end GNCommitProof

/-- Literal relocated output-done tape with the intercepted returned state.
It is defined structurally for either result; no semantic-success proof is used. -/
def gnFirstReturnedConfig (r : GNProgram) (g : SLGate r.inputs.length)
    (hg : r.program.gates[0]? = some g) (res : Bool) :=
  gnReturnConfig res (gnShiftConfig GNM (encodeGN r).length gnEmbed
    (GNM.initialConfig (gnPoint (encodeGN r))).tape
    (g1OutputDoneConfig (gnFirstRequest r g) res) (gnFirstRequest_room hg)
    (g1OutputDoneConfig_head_lt_gnLocalSpan (gnFirstRequest r g) res))

def gnFirstCommitSteps (r : GNProgram) (g : SLGate r.inputs.length) : Nat :=
  (encodeGN r).length + 8*(gnRecordSize (gnGateFields g)+r.inputs.length) +
    4*r.program.gates.length + 39

def gnFirstCommitHead (r : GNProgram) (g : SLGate r.inputs.length) : Nat :=
  4*(gnRecordsStart r + gnRecordSize (gnGateFields g)) +
    if r.program.gates.length = 1 then 8 else 0

private theorem commit_head_safe {r : GNProgram} {g : SLGate r.inputs.length}
    (hg : r.program.gates[0]? = some g) :
    gnFirstCommitHead r g < GNM.tapeLength (encodeGN r).length := by
  have hr := gnFirstRequest_room hg
  have hl := gnRecordSize_le_recordsLength (prior := []) hg
  have hn := encodeGN_length_eq r
  simp only [gnFirstCommitHead, gnRecordsStart, gnLocalSpan, gnOutputSlotsLength] at *
  split <;> omega

def gnFirstCommitConfig (r : GNProgram) (g : SLGate r.inputs.length)
    (hg : r.program.gates[0]? = some g) (res : Bool) :=
  gnCommitConfig (encodeGN r).length (gnFirstCommitHead r g) (commit_head_safe hg)
    (frameListTape ((encodeGNAtFrames r [res] ++
      g1OutputFrames (gnFirstRequest r g) res).flatMap G1Frame.bits))
    (if r.program.gates.length = 1 then .firstCommitTerminal else .firstCommitNext)

private theorem commit_output_overlay {r : GNProgram} {g : SLGate r.inputs.length}
    (hg : r.program.gates[0]? = some g) (res : Bool) :
    gnOverlayTape GNM (encodeGN r).length (gnFirstRequest_room hg)
      (g1OutputDoneConfig (gnFirstRequest r g) res)
      (GNM.initialConfig (gnPoint (encodeGN r))).tape =
    frameListTape ((encodeGNFrames r ++
      g1OutputFrames (gnFirstRequest r g) res).flatMap G1Frame.bits) := by
  have hlen : ((g1OutputFrames (gnFirstRequest r g) res).flatMap G1Frame.bits).length ≤
      gnLocalSpan (encodeG1 (gnFirstRequest r g)).length := by
    simp only [G1Frame.flatMap_bits_length, g1OutputFrames_length, gnLocalSpan,
      encodeG1_length]
    omega
  rw [List.flatMap_append]
  change _ = frameListTape (encodeGN r ++ _)
  funext i
  by_cases hi : (encodeGN r).length ≤ i.val ∧ i.val <
      (encodeGN r).length + gnLocalSpan (encodeG1 (gnFirstRequest r g)).length
  · unfold gnOverlayTape
    rw [dif_pos hi, g1OutputDoneConfig_tape]
    simp only [frameListTape, gnSourceIndex_val, List.getD]
    rw [List.getElem?_append_right hi.1]
  · unfold gnOverlayTape
    rw [dif_neg hi, gnInitialTape_eq_frameListTape]
    by_cases hl : i.val < (encodeGN r).length
    · simp only [frameListTape, List.getD]
      rw [List.getElem?_append_left hl]
    · have he : (encodeGN r ++
          (g1OutputFrames (gnFirstRequest r g) res).flatMap G1Frame.bits).length ≤
          i.val := by simp only [List.length_append]; omega
      simp only [frameListTape, List.getD]
      rw [List.getElem?_eq_none (by omega : (encodeGN r).length ≤ i.val),
        List.getElem?_eq_none he]

namespace GNCommitProof

def boundaryTail {n : Nat} (gs : List (SLGate n)) (pfx : List G1Frame) : List G1Frame :=
  match gs with
  | [] => .finish :: pfx
  | g :: rest => recordBody (gnGateFields g) ++ gnRecordsFrames .bof rest ++
      gnFinalTail false ++ pfx

theorem oldEdge_shape {n : Nat} (gs : List (SLGate n)) (pfx : List G1Frame) :
    oldEdge gs.isEmpty (boundaryTail gs pfx) =
      gnRecordsFrames .bof gs ++ gnFinalTail false ++ pfx := by
  cases gs <;> simp [oldEdge, boundaryTail, recordBody, gnRecordsFrames,
    gnFieldRecordsFrames, g1RecordFrames, gnFinalTail, List.append_assoc]

theorem edge_shape {n : Nat} (gs : List (SLGate n)) (pfx : List G1Frame) (res : Bool) :
    edge gs.isEmpty res (boundaryTail gs pfx) =
      gnRecordsFrames .cursor gs ++ gnFinalTail (if gs.isEmpty then res else false) ++ pfx := by
  cases gs <;> simp [edge, boundaryTail, recordBody, gnRecordsFrames,
    gnFieldRecordsFrames, g1RecordFrames, gnFinalTail, List.append_assoc]

private theorem body_reverse (f : GNField) :
    ∀ x ∈ recordBody f, revAdvance false .scan x = .scan := by
  intro x hx
  cases x <;> first | rfl | simp_all [recordBody]

private theorem records_reverse {n : Nat} (gs : List (SLGate n)) :
    ∀ x ∈ gnRecordsFrames .bof gs, revAdvance false .scan x = .scan := by
  induction gs with
  | nil => simp [gnRecordsFrames, gnFieldRecordsFrames]
  | cons g gs ih =>
    have hs : gnRecordsFrames .bof (g :: gs) = .bof :: recordBody (gnGateFields g) ++
        gnRecordsFrames .bof gs := by
      simp [gnRecordsFrames, gnFieldRecordsFrames, recordBody, g1RecordFrames, List.append_assoc]
    rw [hs]
    intro x hx
    simp only [List.mem_append, List.mem_cons] at hx
    rcases hx with (rfl | hx) | hx
    · rfl
    · exact body_reverse _ x hx
    · exact ih x hx

private theorem prefix_reverse (q : G1Request) :
    ∀ x ∈ g1PrefixFrames q, revAdvance false .scan x = .scan := by
  intro x hx
  cases x <;> first | rfl | simp_all [g1PrefixFrames]

end GNCommitProof

theorem gnFirstReturnedConfig_eq_physical {r : GNProgram} {g : SLGate r.inputs.length}
    (hg : r.program.gates[0]? = some g) (res : Bool)
    (hr : 4*((encodeGNFrames r).length+(g1PrefixFrames (gnFirstRequest r g)).length)-1 <
      GNM.tapeLength (encodeGN r).length) :
    gnFirstReturnedConfig r g hg res =
      gnCommitConfig (encodeGN r).length
        (4*((encodeGNFrames r).length+(g1PrefixFrames (gnFirstRequest r g)).length)-1) hr
        (frameListTape ((encodeGNFrames r ++
          g1OutputFrames (gnFirstRequest r g) res).flatMap G1Frame.bits)) (gnReturnedState res) := by
  apply Configuration.ext_of_components
  · rfl
  · apply Fin.ext
    change (encodeGN r).length + g1OutputExitHead (gnFirstRequest r g) =
      4*((encodeGNFrames r).length+(g1PrefixFrames (gnFirstRequest r g)).length)-1
    have hn := encodeGN_length r
    have hp := g1PrefixFrames_length (gnFirstRequest r g)
    simp only [g1OutputExitHead, g1OutputBase]
    omega
  · exact commit_output_overlay hg res

/-- Genuine local execution from the explicit returned configuration. The
result is a latched input to this pass; semantic success is not a premise. -/
theorem gnCS_firstReturned_commit_exact {r : GNProgram} {g : SLGate r.inputs.length}
    (hg : r.program.gates[0]? = some g) (res : Bool) :
    TM.runConfig (M := GNM) (gnFirstReturnedConfig r g hg res)
      (gnFirstCommitSteps r g) = gnFirstCommitConfig r g hg res := by
  have hp : (g1PrefixFrames (gnFirstRequest r g)).length =
      gnRecordSize (gnGateFields g) + r.inputs.length := by
    simp [g1PrefixFrames_length, gnFirstRequest, gnFieldRequest, gnRecordSize]; omega
  have hw := gnFirstRequest_width r g
  have hn := encodeGN_length r
  have hr := gnFirstRequest_room hg
  simp only [gnLocalSpan] at hr
  have hroom : 4*((encodeGNFrames r).length+(g1PrefixFrames (gnFirstRequest r g)).length) <
      GNM.tapeLength (encodeGN r).length := by omega
  rw [gnFirstReturnedConfig_eq_physical hg res (by omega)]
  cases heq : r.program.gates with
  | nil => simp [heq] at hg
  | cons g0 gs =>
    have hg0 : g0 = g := by simpa [heq] using hg
    subst g0
    let q := gnFirstRequest r g
    have hs : encodeGNFrames r ++ g1PrefixFrames q =
        (G1Frame.bof :: r.inputs.map .data) ++ .output false ::
        (List.replicate gs.length (.output false) ++ [.separator]) ++
        .cursor :: GNCommitProof.recordBody (gnGateFields g) ++
        GNCommitProof.oldEdge gs.isEmpty (GNCommitProof.boundaryTail gs (g1PrefixFrames q)) := by
      rw [GNCommitProof.oldEdge_shape]
      simp [encodeGNFrames, heq, gnAssignFrames, gnSlotFrames, gnRecordsFrames,
        gnFieldRecordsFrames, g1RecordFrames, GNCommitProof.recordBody, gnFinalTail,
        List.replicate_succ, List.append_assoc]
    have hbody := GNCommitProof.core (encodeGN r).length r.inputs gs.length (gnGateFields g)
      (GNCommitProof.boundaryTail gs (g1PrefixFrames q)) [.output res, .finish, .blank]
      gs.isEmpty res (by
        rw [GNCommitProof.oldEdge_shape]
        simp only [List.forall_mem_append]
        refine ⟨GNCommitProof.body_reverse _, ⟨⟨GNCommitProof.records_reverse _, ?_⟩,
          GNCommitProof.prefix_reverse _⟩⟩
        intro x hx
        simp only [gnFinalTail, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl <;> rfl)
      (by
        have hh := congrArg List.length hs
        simp only [List.length_append, List.length_cons, List.length_replicate,
          List.length_singleton, List.length_nil, List.length_map] at hh ⊢
        change 4*((encodeGNFrames r).length+(g1PrefixFrames q).length) < _ at hroom
        omega)
      (by rw [GNCommitProof.oldEdge_shape]; simp only [gnFinalTail, List.length_append,
            List.length_cons, List.length_nil]; omega)
    have hb : (GNCommitProof.recordBody (gnGateFields g)).length+1 =
        gnRecordSize (gnGateFields g) := by
      simp [GNCommitProof.recordBody, gnRecordSize]; omega
    have hout : encodeGNAtFrames r [res] ++ g1OutputFrames q res =
        (G1Frame.bof :: r.inputs.map .data) ++ .data res ::
        (List.replicate gs.length (.output false) ++ [.separator]) ++
        .spent :: GNCommitProof.recordBody (gnGateFields g) ++
        GNCommitProof.edge gs.isEmpty res (GNCommitProof.boundaryTail gs (g1PrefixFrames q)) ++
        [.output res, .finish, .blank] := by
      rw [GNCommitProof.edge_shape]
      cases gs <;>
        simp [encodeGNAtFrames, gnCurrentValues, heq, gnOutputSlotsLength, gnSlotFrames,
          gnRecordsAtFrames, gnRecordFrames, gnRecordsFrames, gnFieldRecordsFrames, g1RecordFrames, GNCommitProof.recordBody,
          gnFinalValue, gnFinalTail, g1OutputFrames, List.append_assoc]
    dsimp only at hbody
    simp only [← hs] at hbody
    simp only [List.length_append] at hbody
    have hclock : 4*((encodeGNFrames r).length+(g1PrefixFrames q).length) +
        4*r.inputs.length + 4*(gs.length+1) + 4*((GNCommitProof.recordBody (gnGateFields g)).length+1)+39 =
        gnFirstCommitSteps r g := by
      simp only [gnFirstCommitSteps, heq, List.length_cons]
      change (g1PrefixFrames q).length = _ at hp
      omega
    rw [hclock] at hbody
    simp only [g1OutputFrames, List.append_assoc] at hbody ⊢
    rw [hbody]
    apply Configuration.ext_of_components
    · change (⟨(0 : Fin 1), if gs.isEmpty then GNState.firstCommitTerminal else .firstCommitNext⟩ : GNM.state) = _
      cases gs <;> simp [gnFirstCommitConfig, gnCommitConfig, Phased.alignedAt, heq] <;> rfl
    · apply Fin.ext
      dsimp only [gnCommitConfig, gnFirstCommitConfig, Phased.alignedAt]
      simp only [gnFirstCommitHead, gnRecordsStart, heq, List.length_cons, List.length_nil,
        List.length_map, List.length_append, List.length_replicate]
      cases gs <;> simp only [List.isEmpty_nil, List.isEmpty_cons, List.length_nil,
        List.length_cons, Bool.false_eq_true, ↓reduceIte] <;> (first | omega | split <;> omega)
    · simpa only [gnCommitConfig, gnFirstCommitConfig, Phased.alignedAt, List.append_assoc,
        g1OutputFrames] using congrArg (fun fs => frameListTape (L := GNM.tapeLength (encodeGN r).length)
        (fs.flatMap G1Frame.bits)) hout.symm

/-- Run-derived canonical ABI and the pure commit relation. The scratch suffix
is part of the full tape; this endpoint does not assert readiness for round two. -/
theorem gnFirstCommit_structure {r : GNProgram} {g : SLGate r.inputs.length}
    (hg : r.program.gates[0]? = some g) (res : Bool) :
    let out := TM.runConfig (M := GNM) (gnFirstReturnedConfig r g hg res) (gnFirstCommitSteps r g)
    out.state = ⟨(0 : Fin 1), if r.program.gates.length = 1 then
      .firstCommitTerminal else .firstCommitNext⟩ ∧
    (out.head : Nat) = gnFirstCommitHead r g ∧
    out.tape = frameListTape ((encodeGNAtFrames r [res] ++
      g1OutputFrames (gnFirstRequest r g) res).flatMap G1Frame.bits) ∧
    gnCommit? r [] res = some ([res], encodeGNAtFrames r [res]) ∧
    gnCurrentValues r [res] = r.inputs ++ [res] ∧
    gnFinalValue r [res] = (if r.program.gates.length = 1 then res else false) := by
  dsimp only
  rw [gnCS_firstReturned_commit_exact hg res]
  refine ⟨rfl, rfl, rfl, ?_, rfl, ?_⟩
  · exact gnCommit?_exact r [] res (gnIndex_lt_length hg)
  · simp [gnFinalValue, eq_comm]

theorem gnFirstCommit_scratch_preserved {r : GNProgram} {g : SLGate r.inputs.length}
    (hg : r.program.gates[0]? = some g) (res : Bool)
    (i : Fin (GNM.tapeLength (encodeGN r).length)) (hi : (encodeGN r).length ≤ i.val) :
    (TM.runConfig (M := GNM) (gnFirstReturnedConfig r g hg res)
      (gnFirstCommitSteps r g)).tape i = (gnFirstReturnedConfig r g hg res).tape i := by
  rw [gnCS_firstReturned_commit_exact hg res]
  change frameListTape ((encodeGNAtFrames r [res] ++
      g1OutputFrames (gnFirstRequest r g) res).flatMap G1Frame.bits) i =
    gnOverlayTape GNM (encodeGN r).length (gnFirstRequest_room hg)
      (g1OutputDoneConfig (gnFirstRequest r g) res)
      (GNM.initialConfig (gnPoint (encodeGN r))).tape i
  rw [commit_output_overlay hg res]
  have hl := encodeGNAt_length r [res] (gnIndex_lt_length hg)
  change ((encodeGNAtFrames r [res]).flatMap G1Frame.bits).length = (encodeGN r).length at hl
  simp only [List.flatMap_append, frameListTape, List.getD]
  rw [List.getElem?_append_right (by omega : ((encodeGNAtFrames r [res]).flatMap G1Frame.bits).length ≤ i.val),
    List.getElem?_append_right (show ((encodeGNFrames r).flatMap G1Frame.bits).length ≤ i.val from hi), hl]
  rfl

/-- Composition from the actual encoded initial machine run; hs is required
only to identify successful evaluation with the supplied returned result. -/
theorem gnCS_encodeGN_firstCommit_exact {r : GNProgram} {g : SLGate r.inputs.length}
    (hg : r.program.gates[0]? = some g) (res : Bool)
    (hs : (gnFirstRequest r g).spec = some res) :
    TM.runConfig (M := GNM) (GNM.initialConfig (gnPoint (encodeGN r)))
      (gnFirstLaunchSteps r g + (g1GateDoneSteps (gnFirstRequest r g)+1) +
        gnFirstCommitSteps r g) = gnFirstCommitConfig r g hg res := by
  rw [runConfig_add, gnCS_encodeGN_firstReturned_exact hg res hs]
  exact gnCS_firstReturned_commit_exact hg res

end Pnp3.Internal.PsubsetPpoly.TM
