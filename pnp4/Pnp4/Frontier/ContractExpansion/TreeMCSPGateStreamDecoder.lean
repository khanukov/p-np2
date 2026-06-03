import Pnp4.Frontier.ContractExpansion.TreeMCSPGateRecordDecoder
import Pnp4.Frontier.ContractExpansion.TreeMCSPLoopUntilSink

/-!
# On-tape gate-record stream decoder (NP-verifier track — decoder brick D2)

The on-tape decoder for a contiguous stream of gate records (`TM_VERIFIER_STRATEGY.md` §6k): loop the
one-record decoder `gateOneRecordDecoder` (D1b) with the head-advancing self-terminating loop
`loopUntilSink`, halting at the decoder's **malformed sink** (phase `13`, reached on a `1^5` tag), which
the stream layout uses as the **end-of-stream marker**.  Each loop pass walks one record and re-enters
at the next record's start; the loop halts when it meets the end marker.

```
gateStreamDecoder := loopUntilSink gateOneRecordDecoder ⟨13⟩
```

This brick ships the **definition** and its **structural** lemmas (phase counts, `neverMovesLeft`
inherited from D1b through the loop combinator).  The run behaviour — discharging `loopUntilSink`'s
`reachesSink` obligations from `gateOneRecordDecoder`'s per-tag traversal (a record advances to accept
`12`) and malformed-sink behaviour (the end marker reaches `13`) on the *composed* machine — is the
documented follow-up, mirroring how the seqP2 lemmas re-derive D1b on a composed machine.

**Progress classification (AGENTS.md): Infrastructure** — toolkit toward the NP-membership leg; it
builds no verifier and proves no separation.  All surfaces carry only the standard
`[propext, Classical.choice, Quot.sound]` triple.
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM

/-- The on-tape gate-record stream decoder: the head-advancing loop over the one-record decoder,
halting at its malformed sink (phase `13`), which doubles as the end-of-stream marker. -/
def gateStreamDecoder : ConstStatePhasedProgram Unit :=
  loopUntilSink gateOneRecordDecoder ⟨13, by simp⟩

@[simp] theorem gateStreamDecoder_numPhases : gateStreamDecoder.numPhases = 14 := rfl

@[simp] theorem gateStreamDecoder_startPhase_val : (gateStreamDecoder.startPhase : Nat) = 0 := rfl

@[simp] theorem gateStreamDecoder_acceptPhase_val : (gateStreamDecoder.acceptPhase : Nat) = 13 := rfl

/-- The stream decoder never moves the head left — inherited from `gateOneRecordDecoder` through the
loop combinator (the loop's control steps idle; the body steps are the decoder's, which advance right). -/
theorem gateStreamDecoder_neverMovesLeft : TMNeverMovesLeft (gateStreamDecoder.toPhased.toTM) :=
  loopUntilSink_neverMovesLeft gateOneRecordDecoder ⟨13, by simp⟩
    gateOneRecordDecoder_transition_move

/-! ### Transition bridge: the stream decoder runs the one-record decoder at body phases

At any phase `< 12` (i.e. not the one-record decoder's accept `12` or its sink `13`), the stream
decoder's transition is exactly the one-record decoder's — the loop only intercepts the accept/sink
phases.  This bridges D1b's transition behaviour onto `gateStreamDecoder`, so its run behaviour can be
re-derived on the composed machine (the `Configuration` types of the two `toTM`s are not defeq, so D1b's
lemmas cannot transfer directly; this bridge re-derives them at the transition level instead). -/
theorem gateStreamDecoder_transition_body (i : Fin 14) (s : Unit) (b : Bool) (hi : i.val < 12) :
    gateStreamDecoder.transition i s b = gateOneRecordDecoder.transition i s b := by
  have h1 : i ≠ gateOneRecordDecoder.acceptPhase :=
    Fin.ne_of_val_ne (by rw [gateOneRecordDecoder_acceptPhase_val]; omega)
  have h2 : i ≠ (⟨13, by simp⟩ : Fin gateOneRecordDecoder.numPhases) :=
    Fin.ne_of_val_ne (by simp; omega)
  exact loopUntilSink_transition_body gateOneRecordDecoder ⟨13, by simp⟩ h1 h2 s b

/-! ### Re-derived single-step lemmas (tag-read phases) via the bridge

Each is the `gateStreamDecoder` analogue of the corresponding `gateOneRecordDecoder` single-step,
obtained by `toTM_stepConfig_*` + the transition bridge + D1b's transition reduction.  These seed the
run-behaviour re-derivation (scanning / dispatch / per-tag traversal) on the composed machine. -/

/-- Tag-read `1` at phase `i < 4`: advance to phase `i + 1`. -/
theorem gateStreamDecoder_stepConfig_tag_one_phase {L : Nat}
    (c : Configuration (M := gateStreamDecoder.toPhased.toTM) L) {i : Fin 14} {s : Unit}
    (hi : i.val < 4) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := gateStreamDecoder.toPhased.toTM) c).state).fst.val = i.val + 1 := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_phase gateStreamDecoder c hstate,
    gateStreamDecoder_transition_body i s (c.tape c.head) (by omega)]
  simp only [gateOneRecordDecoder, dif_pos hi, hbit, if_true]

/-- Tag-read `1` at phase `i < 4`: advance the head by one. -/
theorem gateStreamDecoder_stepConfig_tag_one_head {L : Nat}
    (c : Configuration (M := gateStreamDecoder.toPhased.toTM) L) {i : Fin 14} {s : Unit}
    (hi : i.val < 4) (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true)
    (hbound : (c.head : Nat) + 1 < gateStreamDecoder.toPhased.toTM.tapeLength L) :
    ((TM.stepConfig (M := gateStreamDecoder.toPhased.toTM) c).head : Nat) = (c.head : Nat) + 1 := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_head gateStreamDecoder c hstate]
  have hmove : (gateStreamDecoder.transition i s (c.tape c.head)).2.2.2 = Move.right := by
    rw [gateStreamDecoder_transition_body i s (c.tape c.head) (by omega)]
    simp only [gateOneRecordDecoder, dif_pos hi, hbit, if_true]
  rw [hmove]
  simp only [Configuration.moveHead, dif_pos hbound]

end ContractExpansion
end Frontier
end Pnp4
