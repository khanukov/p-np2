import Pnp4.Frontier.ContractExpansion.TreeMCSPDriverCorridor

/-!
# `emitTape` — D2t-5b (Block A4a): the output-region update of a gate emit

Every emitting arm (`const`, `input`, the settle-pop) does the same thing to the output region:
**append the new gate record** at the frontier marker `FM` and replant `FM` just past it.  The unary
gate-count prefix is **static** under the corridor protocol: it spells `unaryField z.outCount` (the
*final* gate count, planted once by the init bridge) throughout the run, because the count field
lies **left of the record stream** and the record stream is not backward-parseable (operand counts
vary and `unaryField 0 = [0]` / `const = [1,0,b]` create `0,0` runs inside the stream), so no sound
machine route from the driver's home can reach the count cells once a record exists.  The emit
therefore touches exactly two places: the record window and the frontier marker.

`emitTape` is that output-region transformer; `emitTape_output_window` proves it extends the
invariant's output window for `out` into the one for `out ++ [g]` (the static count prefix is
untouched, the records grow one record right at the old `FM`); `emitTape_FM` plants the new
frontier marker; `emitTape_off` is the off-region identity.  These are the reusable output-region
facts the emit keystones consume; the cursor-area and value-stack updates are handled separately
(as in the node keystone).

**Progress classification (AGENTS.md): Infrastructure** — a pure tape-window update lemma for the
verified gate-stream codec; builds no machine and proves no separation.  Standard `[propext,
Classical.choice, Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-- The record stream over a snoc: the new gate's record is appended on the right. -/
theorem encodeGateRecordStream_snoc {n : Nat} (out : List (SLGate n)) (g : SLGate n) :
    encodeGateRecordStream (out ++ [g]) = encodeGateRecordStream out ++ encodeGateRecord g := by
  induction out with
  | nil => simp [encodeGateRecordStream]
  | cons a l ih => simp only [List.cons_append, encodeGateRecordStream, ih, List.append_assoc]

/-- The record stream's length over a snoc. -/
theorem encodeGateRecordStream_snoc_length {n : Nat} (out : List (SLGate n)) (g : SLGate n) :
    (encodeGateRecordStream (out ++ [g])).length
      = (encodeGateRecordStream out).length + (encodeGateRecord g).length := by
  rw [encodeGateRecordStream_snoc, List.length_append]

/-- The output-region transformer of a gate emit: the new record `rec` at the old frontier
`[fm, fm + |rec|)`; the new frontier marker `1` at `fm + |rec|`; else unchanged.  (The unary count
prefix is static — see the module docstring.) -/
def emitTape {L : Nat} (tape : Fin L → Bool) (fm : Nat) (rec : List Bool) (q : Fin L) : Bool :=
  if fm ≤ (q : Nat) ∧ (q : Nat) < fm + rec.length then rec.getD ((q : Nat) - fm) false
  else if (q : Nat) = fm + rec.length then true
  else tape q

/-- `emitTape` is the identity off the record window `[fm, fm + |rec|)` and the new frontier
`fm + |rec|`. -/
theorem emitTape_off {L : Nat} (tape : Fin L → Bool) (fm : Nat) (rec : List Bool) (q : Fin L)
    (h2 : ¬ (fm ≤ (q : Nat) ∧ (q : Nat) < fm + rec.length))
    (h3 : (q : Nat) ≠ fm + rec.length) : emitTape tape fm rec q = tape q := by
  unfold emitTape
  rw [if_neg h2, if_neg h3]

/-- **The output window after a gate emit.**  If, before the emit, the combined output window at
`base = workBase − 1 − N` spells `unaryField N ++ encodeGateRecordStream out` (the static count
prefix `N` plus the records so far), then after `emitTape` at the frontier
`fm = base + |window|` the same base spells `unaryField N ++ encodeGateRecordStream (out ++ [g])` —
the invariant's output clause for the emitted state. -/
theorem emitTape_output_window {n L : Nat} (tape : Fin L → Bool) (base N : Nat)
    (out : List (SLGate n)) (g : SLGate n)
    (hwin : windowSpells tape base (unaryField N ++ encodeGateRecordStream out))
    (hfit : base + (unaryField N ++ encodeGateRecordStream out).length
        + (encodeGateRecord g).length ≤ L) :
    windowSpells (emitTape tape
        (base + (unaryField N ++ encodeGateRecordStream out).length)
        (encodeGateRecord g))
      base
      (unaryField N ++ encodeGateRecordStream (out ++ [g])) := by
  obtain ⟨hwfit, hwc⟩ := hwin
  set body := unaryField N ++ encodeGateRecordStream out with hbody
  set rec := encodeGateRecord g with hrec
  have htarget : unaryField N ++ encodeGateRecordStream (out ++ [g]) = body ++ rec := by
    rw [encodeGateRecordStream_snoc, hbody, hrec, List.append_assoc]
  rw [htarget]
  refine ⟨by rw [List.length_append]; omega, fun q hlo hhi => ?_⟩
  rw [List.length_append] at hhi
  unfold emitTape
  by_cases hq : base + body.length ≤ (q : Nat) ∧ (q : Nat) < base + body.length + rec.length
  · -- the freshly written record
    rw [if_pos hq,
      List.getD_append_right body rec false ((q : Nat) - base) (by omega)]
    congr 1
    omega
  · -- inside the old window: untouched (also not the new frontier cell, which is past the window)
    rw [if_neg hq, if_neg (by omega : ¬ (q : Nat) = base + body.length + rec.length),
      hwc q hlo (by omega),
      List.getD_append body rec false ((q : Nat) - base) (by omega)]

/-- After `emitTape`, the new frontier marker sits at `fm + |rec|`. -/
theorem emitTape_FM {L : Nat} (tape : Fin L → Bool) (fm : Nat) (rec : List Bool) :
    ∀ q : Fin L, (q : Nat) = fm + rec.length → emitTape tape fm rec q = true := by
  intro q hq
  unfold emitTape
  rw [if_neg (by omega), if_pos hq]

end ContractExpansion
end Frontier
end Pnp4
