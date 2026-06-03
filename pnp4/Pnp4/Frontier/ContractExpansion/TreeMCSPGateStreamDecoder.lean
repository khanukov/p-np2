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

end ContractExpansion
end Frontier
end Pnp4
