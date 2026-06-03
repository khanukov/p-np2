import Pnp4.Frontier.ContractExpansion.TreeMCSPGateStreamDecoder
import Pnp4.Frontier.ContractExpansion.TreeMCSPGateStreamLayout

/-!
# Stream-decoder termination on a well-formed gate stream (NP-verifier track — decoder brick D2, capstone)

`gateStreamDecoder` (`TreeMCSPGateStreamDecoder.lean`) is the head-advancing loop
`loopUntilSink gateOneRecordDecoder ⟨13⟩` over the one-record decoder.  Its per-record run behaviour is
proven there (the five `gateStreamDecoder_runConfig_{input,const,not,and,or}` traversals reach accept
`12` after exactly `gateRecordSize g` steps, head advanced past the record, tape unchanged); the loop
combinator's re-entry (`loopUntilSink_runConfig_oneIter`) and malformed-sink behaviour
(`gateStreamDecoder_runConfig_malformed`) are the two control facts.

This brick **discharges the central `loopUntilSink` obligation for the concrete stream encoding**: a tape
whose witness region holds `encodeGateRecordStream gs` (the D2 spec layout, `TreeMCSPGateStreamLayout.lean`)
followed by the end-of-stream marker `1^5` drives the loop to its sink phase `13` — i.e. the loop
*terminates* on a well-formed gate stream, consuming one record per pass and halting at the marker.  This
is the head-advancing analogue of a row loop's termination, and the precise statement the eventual
interpreter relies on to know the witness walk halts.

The bridge from "the tape holds the encoded stream" to the per-cell predicates the traversals consume is
`TapeHoldsAt`, a structural "the tape window starting at `h` equals the bit list" predicate: it splits
along `++` (`TapeHoldsAt_append`) exactly as the record layout concatenates its unary fields, and a unary
field's window yields the traversals' ones/terminator hypotheses (`TapeHoldsAt_unaryField`).  The main
theorem is then a gate-list induction: the `cons` step takes one per-record traversal + one loop re-entry
(`gateRecordSize g + 1` steps) and re-establishes the hypothesis on the tail (the head advanced exactly
past record `g`, the tape unchanged); the `nil` base meets the `1^5` marker and routes to the sink.

**Progress classification (AGENTS.md): Infrastructure** — toolkit toward the NP-membership leg of
`VerifiedNPDAGLowerBoundSource`; it builds no verifier and proves no separation.  All surfaces carry only
the standard `[propext, Classical.choice, Quot.sound]` triple.
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-! ### `TapeHoldsAt`: the tape window starting at `h` equals a bit list

A structural predicate matching the per-cell shape the traversals consume (`∀ p, (p : Nat) = … →
c.tape p = …`), so no `h < tapeLength` side-proof is needed.  It splits along `++` exactly as the record
layout concatenates fields. -/

/-- `TapeHoldsAt c h bs`: the tape of `c`, read rightward from cell `h`, spells out the bit list `bs`. -/
def TapeHoldsAt {L : Nat} (c : Configuration (M := gateStreamDecoder.toPhased.toTM) L) :
    Nat → List Bool → Prop
  | _, [] => True
  | h, b :: bs =>
      (∀ p : Fin (gateStreamDecoder.toPhased.toTM.tapeLength L), (p : Nat) = h → c.tape p = b)
      ∧ TapeHoldsAt c (h + 1) bs

/-- `TapeHoldsAt` of a concatenation splits into the two windows — the structural workhorse, mirroring
the record layout's field concatenation. -/
theorem TapeHoldsAt_append {L : Nat} (c : Configuration (M := gateStreamDecoder.toPhased.toTM) L)
    (xs ys : List Bool) (h : Nat) :
    TapeHoldsAt c h (xs ++ ys) ↔ TapeHoldsAt c h xs ∧ TapeHoldsAt c (h + xs.length) ys := by
  induction xs generalizing h with
  | nil => simp [TapeHoldsAt]
  | cons x xs ih =>
      simp only [List.cons_append, TapeHoldsAt, List.length_cons, ih (h + 1)]
      have hofs : h + 1 + xs.length = h + (xs.length + 1) := by omega
      rw [hofs]
      tauto

/-- `TapeHoldsAt` depends only on the tape, so it transports along an equal tape (used to carry the
hypothesis to the post-step configuration, whose tape the traversals leave unchanged). -/
theorem TapeHoldsAt_tape_congr {L : Nat}
    (c₁ c₂ : Configuration (M := gateStreamDecoder.toPhased.toTM) L) (h : Nat) (bs : List Bool)
    (htape : c₁.tape = c₂.tape) :
    TapeHoldsAt c₁ h bs ↔ TapeHoldsAt c₂ h bs := by
  induction bs generalizing h with
  | nil => simp [TapeHoldsAt]
  | cons b bs ih =>
      constructor
      · rintro ⟨hh, ht⟩
        exact ⟨fun p hp => by rw [← htape]; exact hh p hp, (ih (h + 1)).mp ht⟩
      · rintro ⟨hh, ht⟩
        exact ⟨fun p hp => by rw [htape]; exact hh p hp, (ih (h + 1)).mpr ht⟩

/-- Extract the cell predicate at the head of a window. -/
theorem TapeHoldsAt_replicate_true {L : Nat}
    (c : Configuration (M := gateStreamDecoder.toPhased.toTM) L) :
    ∀ (k h : Nat), TapeHoldsAt c h (List.replicate k true) →
      ∀ p : Fin (gateStreamDecoder.toPhased.toTM.tapeLength L),
        h ≤ (p : Nat) → (p : Nat) < h + k → c.tape p = true := by
  intro k
  induction k with
  | zero => intro h _ht p hp1 hp2; omega
  | succ k ih =>
      intro h ht p hp1 hp2
      rw [List.replicate_succ] at ht
      obtain ⟨hhead, htail⟩ := ht
      rcases Nat.eq_or_lt_of_le hp1 with hpe | hpl
      · exact hhead p hpe.symm
      · exact ih (h + 1) htail p hpl (by omega)

/-- A unary field's window yields the traversals' "ones up to `k`" and "terminator at `k`" hypotheses. -/
theorem TapeHoldsAt_unaryField {L : Nat}
    (c : Configuration (M := gateStreamDecoder.toPhased.toTM) L) (k h : Nat)
    (ht : TapeHoldsAt c h (unaryField k)) :
    (∀ p : Fin (gateStreamDecoder.toPhased.toTM.tapeLength L),
        h ≤ (p : Nat) → (p : Nat) < h + k → c.tape p = true)
      ∧ (∀ p : Fin (gateStreamDecoder.toPhased.toTM.tapeLength L),
        (p : Nat) = h + k → c.tape p = false) := by
  simp only [unaryField] at ht
  rw [TapeHoldsAt_append] at ht
  simp only [List.length_replicate] at ht
  obtain ⟨hones, hterm⟩ := ht
  refine ⟨TapeHoldsAt_replicate_true c k h hones, ?_⟩
  intro p hp
  exact hterm.1 p hp

/-! ### One record on the stream: derive the per-cell predicates and run one traversal

A single lemma over `SLGate`: from `TapeHoldsAt c₀ head (encodeGateRecord g)` (the record's bits on the
tape) it peels the unary fields with `TapeHoldsAt_append`, extracts the ones/terminator predicates with
`TapeHoldsAt_unaryField`, and feeds the matching per-tag traversal — concluding accept `12`, head past the
record, tape unchanged, after exactly `gateRecordSize g` steps. -/
theorem gateStreamDecoder_runConfig_record {L : Nat} {n : Nat} (g : SLGate n)
    (c₀ : Configuration (M := gateStreamDecoder.toPhased.toTM) L)
    (hphase : (c₀.state.fst : Nat) = 0)
    (hb : (c₀.head : Nat) + gateRecordSize g < gateStreamDecoder.toPhased.toTM.tapeLength L)
    (htape : TapeHoldsAt c₀ (c₀.head : Nat) (encodeGateRecord g)) :
    (((TM.runConfig (M := gateStreamDecoder.toPhased.toTM) c₀ (gateRecordSize g)).state).fst : Nat) = 12
      ∧ ((TM.runConfig (M := gateStreamDecoder.toPhased.toTM) c₀ (gateRecordSize g)).head : Nat)
          = (c₀.head : Nat) + gateRecordSize g
      ∧ (TM.runConfig (M := gateStreamDecoder.toPhased.toTM) c₀ (gateRecordSize g)).tape = c₀.tape := by
  cases g with
  | input idx =>
      simp only [encodeGateRecord] at htape
      rw [TapeHoldsAt_append] at htape
      simp only [unaryField_length] at htape
      obtain ⟨htag0, hrest⟩ := htape
      obtain ⟨_, htag⟩ := TapeHoldsAt_unaryField c₀ 0 _ htag0
      obtain ⟨hones, hterm⟩ := TapeHoldsAt_unaryField c₀ idx.val _ hrest
      refine gateStreamDecoder_runConfig_input idx c₀ hphase hb ?_ ?_ ?_
      · intro p hp; exact htag p (by omega)
      · intro p hp1 hp2; exact hones p (by omega) (by omega)
      · intro p hp; exact hterm p (by omega)
  | const b =>
      simp only [encodeGateRecord] at htape
      rw [TapeHoldsAt_append] at htape
      obtain ⟨hone_uf, _hlit⟩ := htape
      obtain ⟨hone, hterm⟩ := TapeHoldsAt_unaryField c₀ 1 _ hone_uf
      refine gateStreamDecoder_runConfig_const (n := n) b c₀ hphase hb ?_ ?_
      · intro p hp1 hp2; exact hone p (by omega) (by omega)
      · intro p hp; exact hterm p (by omega)
  | notGate k =>
      simp only [encodeGateRecord] at htape
      rw [TapeHoldsAt_append] at htape
      simp only [unaryField_length] at htape
      obtain ⟨htag_uf, href_uf⟩ := htape
      obtain ⟨htagones, htagterm⟩ := TapeHoldsAt_unaryField c₀ 2 _ htag_uf
      obtain ⟨hrefones, hrefterm⟩ := TapeHoldsAt_unaryField c₀ k _ href_uf
      refine gateStreamDecoder_runConfig_not (n := n) k c₀ hphase hb ?_ ?_ ?_ ?_
      · intro p hp1 hp2; exact htagones p (by omega) (by omega)
      · intro p hp; exact htagterm p (by omega)
      · intro p hp1 hp2; exact hrefones p (by omega) (by omega)
      · intro p hp; exact hrefterm p (by omega)
  | andGate k l =>
      simp only [encodeGateRecord] at htape
      rw [TapeHoldsAt_append, TapeHoldsAt_append] at htape
      simp only [List.length_append, unaryField_length] at htape
      obtain ⟨⟨htag_uf, h1_uf⟩, h2_uf⟩ := htape
      obtain ⟨htagones, htagterm⟩ := TapeHoldsAt_unaryField c₀ 3 _ htag_uf
      obtain ⟨h1ones, h1term⟩ := TapeHoldsAt_unaryField c₀ k _ h1_uf
      obtain ⟨h2ones, h2term⟩ := TapeHoldsAt_unaryField c₀ l _ h2_uf
      refine gateStreamDecoder_runConfig_and (n := n) k l c₀ hphase hb ?_ ?_ ?_ ?_ ?_ ?_
      · intro p hp1 hp2; exact htagones p (by omega) (by omega)
      · intro p hp; exact htagterm p (by omega)
      · intro p hp1 hp2; exact h1ones p (by omega) (by omega)
      · intro p hp; exact h1term p (by omega)
      · intro p hp1 hp2; exact h2ones p (by omega) (by omega)
      · intro p hp; exact h2term p (by omega)
  | orGate k l =>
      simp only [encodeGateRecord] at htape
      rw [TapeHoldsAt_append, TapeHoldsAt_append] at htape
      simp only [List.length_append, unaryField_length] at htape
      obtain ⟨⟨htag_uf, h1_uf⟩, h2_uf⟩ := htape
      obtain ⟨htagones, htagterm⟩ := TapeHoldsAt_unaryField c₀ 4 _ htag_uf
      obtain ⟨h1ones, h1term⟩ := TapeHoldsAt_unaryField c₀ k _ h1_uf
      obtain ⟨h2ones, h2term⟩ := TapeHoldsAt_unaryField c₀ l _ h2_uf
      refine gateStreamDecoder_runConfig_or (n := n) k l c₀ hphase hb ?_ ?_ ?_ ?_ ?_ ?_
      · intro p hp1 hp2; exact htagones p (by omega) (by omega)
      · intro p hp; exact htagterm p (by omega)
      · intro p hp1 hp2; exact h1ones p (by omega) (by omega)
      · intro p hp; exact h1term p (by omega)
      · intro p hp1 hp2; exact h2ones p (by omega) (by omega)
      · intro p hp; exact h2term p (by omega)

/-- **End-of-stream marker.**  Five leading `1`s (`1^5`) at the start phase drive the tag scan to phase
`4` and then route to the sink phase `13`, advancing the head by exactly `5` and leaving the tape
unchanged.  The full run-behaviour version of `gateStreamDecoder_runConfig_malformed` (adds the head and
tape clauses), used as the `nil` base of the stream induction. -/
theorem gateStreamDecoder_runConfig_marker {L : Nat}
    (c₀ : Configuration (M := gateStreamDecoder.toPhased.toTM) L)
    (hphase : (c₀.state.fst : Nat) = 0)
    (hb : (c₀.head : Nat) + 4 + 1 < gateStreamDecoder.toPhased.toTM.tapeLength L)
    (hones : ∀ p : Fin (gateStreamDecoder.toPhased.toTM.tapeLength L),
      (c₀.head : Nat) ≤ (p : Nat) → (p : Nat) < (c₀.head : Nat) + 5 → c₀.tape p = true) :
    (((TM.runConfig (M := gateStreamDecoder.toPhased.toTM) c₀ (4 + 1)).state).fst : Nat) = 13
      ∧ ((TM.runConfig (M := gateStreamDecoder.toPhased.toTM) c₀ (4 + 1)).head : Nat)
          = (c₀.head : Nat) + 5
      ∧ (TM.runConfig (M := gateStreamDecoder.toPhased.toTM) c₀ (4 + 1)).tape = c₀.tape := by
  obtain ⟨hph, hhd, htp⟩ := gateStreamDecoder_runConfig_tagscan c₀ hphase 4 (by omega) (by omega)
    (fun p hp1 hp2 => hones p hp1 (by omega))
  rw [TM.runConfig_succ]
  set c := TM.runConfig (M := gateStreamDecoder.toPhased.toTM) c₀ 4 with hc
  have hi4 : (c.state.fst : Nat) = 4 := by rw [hph]
  have hbit : c.tape c.head = true := by
    rw [htp]; exact hones c.head (by rw [hhd]; omega) (by rw [hhd]; omega)
  have hbnd : (c.head : Nat) + 1 < gateStreamDecoder.toPhased.toTM.tapeLength L := by
    rw [hhd]; omega
  refine ⟨?_, ?_, ?_⟩
  · rw [gateStreamDecoder_stepConfig_phase4_one_phase c (i := c.state.fst) (s := c.state.snd) hi4 rfl
      hbit]
  · rw [gateStreamDecoder_stepConfig_phase4_head c (i := c.state.fst) (s := c.state.snd) hi4 rfl hbnd]
    omega
  · rw [gateStreamDecoder_stepConfig_tape c (i := c.state.fst) (s := c.state.snd) rfl, htp]

/-! ### Capstone: the loop reaches its sink on a well-formed stream + marker -/

/-- **Stream-decoder termination.**  If the tape from `c₀.head` holds `encodeGateRecordStream gs` followed
by the end-of-stream marker `1^5` (`List.replicate 5 true`), and `c₀` is at the start phase `0`, then the
stream decoder reaches its sink phase `13` after some number of steps — it consumes one record per loop
pass and halts at the marker — with the head at exactly the end of the consumed stream
(`c₀.head + |encodeGateRecordStream gs| + 5`, the `+5` for the marker scan) and the tape unchanged (the
decoder is read-only).  Discharges the `loopUntilSink.reachesSink` obligation for the concrete D2 stream
encoding, to the toolkit's full run-behaviour standard (phase + head + tape).  Induction on the gate
list: the `cons` step is one per-record traversal (`gateStreamDecoder_runConfig_record`) plus one loop
re-entry (`loopUntilSink_runConfig_oneIter`); the `nil` base meets the marker
(`gateStreamDecoder_runConfig_marker`). -/
theorem gateStreamDecoder_runConfig_reachesSink {L : Nat} {n : Nat} (gs : List (SLGate n))
    (c₀ : Configuration (M := gateStreamDecoder.toPhased.toTM) L)
    (hphase : (c₀.state.fst : Nat) = 0)
    (hb : (c₀.head : Nat) + (encodeGateRecordStream gs).length + 5
        < gateStreamDecoder.toPhased.toTM.tapeLength L)
    (htape : TapeHoldsAt c₀ (c₀.head : Nat)
        (encodeGateRecordStream gs ++ List.replicate 5 true)) :
    ∃ t, (((TM.runConfig (M := gateStreamDecoder.toPhased.toTM) c₀ t).state).fst : Nat) = 13
      ∧ ((TM.runConfig (M := gateStreamDecoder.toPhased.toTM) c₀ t).head : Nat)
          = (c₀.head : Nat) + (encodeGateRecordStream gs).length + 5
      ∧ (TM.runConfig (M := gateStreamDecoder.toPhased.toTM) c₀ t).tape = c₀.tape := by
  induction gs generalizing c₀ with
  | nil =>
      have ht5 : TapeHoldsAt c₀ (c₀.head : Nat) (List.replicate 5 true) := by
        simpa [encodeGateRecordStream] using htape
      have hbm : (c₀.head : Nat) + 4 + 1 < gateStreamDecoder.toPhased.toTM.tapeLength L := by
        simp only [encodeGateRecordStream, List.length_nil] at hb; omega
      obtain ⟨hmp, hmh, hmt⟩ :=
        gateStreamDecoder_runConfig_marker c₀ hphase hbm (TapeHoldsAt_replicate_true c₀ 5 _ ht5)
      exact ⟨4 + 1, hmp, by rw [hmh]; simp [encodeGateRecordStream], hmt⟩
  | cons g gs ih =>
      simp only [encodeGateRecordStream, List.length_append, encodeGateRecord_length] at hb
      -- `hb : c₀.head + (gateRecordSize g + (encodeGateRecordStream gs).length) + 5 < tapeLength`
      have htape' : TapeHoldsAt c₀ (c₀.head : Nat)
          (encodeGateRecord g ++ (encodeGateRecordStream gs ++ List.replicate 5 true)) := by
        simpa [encodeGateRecordStream, List.append_assoc] using htape
      rw [TapeHoldsAt_append] at htape'
      obtain ⟨htape_rec, htape_rest⟩ := htape'
      have hbrec : (c₀.head : Nat) + gateRecordSize g
          < gateStreamDecoder.toPhased.toTM.tapeLength L := by omega
      obtain ⟨hph, hhd, htp⟩ := gateStreamDecoder_runConfig_record g c₀ hphase hbrec htape_rec
      -- One loop re-entry: from accept `12`, the back-edge returns to start `0` (head unchanged).
      have hbody : (TM.runConfig (M := gateStreamDecoder.toPhased.toTM) c₀ (gateRecordSize g)).state.fst
          = gateOneRecordDecoder.acceptPhase :=
        Fin.ext (by rw [hph, gateOneRecordDecoder_acceptPhase_val])
      obtain ⟨hreenter_phase, hreenter_head⟩ :=
        loopUntilSink_runConfig_oneIter gateOneRecordDecoder ⟨13, by simp⟩ (gateRecordSize g) c₀ hbody
      -- Restate the re-entry facts in `gateStreamDecoder` form (defeq to the `loopUntilSink …` form).
      have hrh : (TM.runConfig (M := gateStreamDecoder.toPhased.toTM) c₀ (gateRecordSize g + 1)).head
          = (TM.runConfig (M := gateStreamDecoder.toPhased.toTM) c₀ (gateRecordSize g)).head :=
        hreenter_head
      -- The post-step configuration `runConfig c₀ (gateRecordSize g + 1)`: phase 0, head past record, tape fixed.
      have hphase_c1 : ((TM.runConfig (M := gateStreamDecoder.toPhased.toTM) c₀
          (gateRecordSize g + 1)).state.fst : Nat) = 0 :=
        hreenter_phase.trans gateOneRecordDecoder_startPhase_val
      have hoff : ((TM.runConfig (M := gateStreamDecoder.toPhased.toTM) c₀ (gateRecordSize g + 1)).head
          : Nat) = (c₀.head : Nat) + (encodeGateRecord g).length := by
        rw [hrh, hhd, encodeGateRecord_length]
      have htc1 : (TM.runConfig (M := gateStreamDecoder.toPhased.toTM) c₀ (gateRecordSize g + 1)).tape
          = c₀.tape := by
        rw [TM.runConfig_succ,
          gateStreamDecoder_stepConfig_tape
            (TM.runConfig (M := gateStreamDecoder.toPhased.toTM) c₀ (gateRecordSize g))
            (i := (TM.runConfig (M := gateStreamDecoder.toPhased.toTM) c₀ (gateRecordSize g)).state.fst)
            (s := (TM.runConfig (M := gateStreamDecoder.toPhased.toTM) c₀ (gateRecordSize g)).state.snd)
            rfl]
        exact htp
      have hb_c1 : ((TM.runConfig (M := gateStreamDecoder.toPhased.toTM) c₀ (gateRecordSize g + 1)).head
          : Nat) + (encodeGateRecordStream gs).length + 5
          < gateStreamDecoder.toPhased.toTM.tapeLength L := by
        rw [hoff, encodeGateRecord_length]; omega
      have htape_c1 : TapeHoldsAt
          (TM.runConfig (M := gateStreamDecoder.toPhased.toTM) c₀ (gateRecordSize g + 1))
          ((TM.runConfig (M := gateStreamDecoder.toPhased.toTM) c₀ (gateRecordSize g + 1)).head : Nat)
          (encodeGateRecordStream gs ++ List.replicate 5 true) := by
        rw [hoff]
        exact (TapeHoldsAt_tape_congr _ c₀ _ _ htc1).mpr htape_rest
      obtain ⟨t, htp13, hthead, httape⟩ :=
        ih (TM.runConfig (M := gateStreamDecoder.toPhased.toTM) c₀ (gateRecordSize g + 1))
          hphase_c1 hb_c1 htape_c1
      refine ⟨(gateRecordSize g + 1) + t, ?_, ?_, ?_⟩
      · rw [TM.runConfig_add]; exact htp13
      · rw [TM.runConfig_add, hthead, hoff, encodeGateRecord_length]
        simp only [encodeGateRecordStream, List.length_append, encodeGateRecord_length]; omega
      · rw [TM.runConfig_add, httape]; exact htc1

end ContractExpansion
end Frontier
end Pnp4
