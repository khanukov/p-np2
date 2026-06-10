import Pnp4.Frontier.ContractExpansion.TreeMCSPDriverCorridor

/-!
# `emitTape` — D2t-5b (Block A4a): the output-region update of a leaf emit

Both leaf arms (`const`, `input`) do the same thing to the output region: **increment the unary gate
count** (prepend one `1` at the count field's left, `out.length → out.length + 1`) and **append the
new gate record** at the frontier marker `FM`, replanting `FM` just past it.  `emitTape` is that
output-region transformer, and `emitTape_output_window` proves it turns the invariant's output window
for `out` into the one for `out ++ [g]`:

```
unaryField (out.length+1) ++ encodeGateRecordStream (out ++ [g])
  = [1] ++ (unaryField out.length ++ encodeGateRecordStream out) ++ encodeGateRecord g
```

i.e. the count window grows one cell **left** of its old anchor, the records grow one record **right**
at the old `FM`, and everything between is untouched — so the new window still spells
`encodeGateStream (out ++ [g])` (`driverStrongInv_out_encodeGateStream`'s shape).  `emitTape_FM` plants
the new frontier marker.  These are the reusable output-region facts the `const`/`input` keystones
consume; the cursor-area and value-stack updates are handled separately (as in the node keystone).

**Progress classification (AGENTS.md): Infrastructure** — a pure tape-window update lemma for the
verified gate-stream codec; builds no machine and proves no separation.  Standard `[propext,
Classical.choice, Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-- The output-region transformer of a leaf emit: a fresh `1` at the count field's new left end
(`oc − 1`, where `oc = workBase − 1 − out.length` is the old count anchor); the new record `rec` at
the old frontier `[fm, fm + |rec|)`; the new frontier marker `1` at `fm + |rec|`; else unchanged. -/
def emitTape {L : Nat} (tape : Fin L → Bool) (oc fm : Nat) (rec : List Bool) (q : Fin L) : Bool :=
  if (q : Nat) = oc - 1 then true
  else if fm ≤ (q : Nat) ∧ (q : Nat) < fm + rec.length then rec.getD ((q : Nat) - fm) false
  else if (q : Nat) = fm + rec.length then true
  else tape q

/-- The gate-stream window grows by exactly `[1]` on the left and `encodeGateRecord g` on the right:
`unaryField (c+1) ++ encodeGateRecordStream (out ++ [g])
  = true :: (unaryField c ++ encodeGateRecordStream out) ++ encodeGateRecord g`, where `c = |out|`. -/
theorem gateStream_emit_eq {n : Nat} (out : List (SLGate n)) (g : SLGate n) :
    unaryField (out.length + 1) ++ encodeGateRecordStream (out ++ [g])
      = (true :: (unaryField out.length ++ encodeGateRecordStream out)) ++ encodeGateRecord g := by
  have hrec : encodeGateRecordStream (out ++ [g])
      = encodeGateRecordStream out ++ encodeGateRecord g := by
    induction out with
    | nil => simp [encodeGateRecordStream]
    | cons a l ih => simp only [List.cons_append, encodeGateRecordStream, ih, List.append_assoc]
  have hcount : unaryField (out.length + 1) = true :: unaryField out.length := by
    simp [unaryField, List.replicate_succ]
  rw [hrec, hcount]
  simp [List.append_assoc]

/-- **The output window after a leaf emit.**  If, before the emit, the combined output window at
`oc = workBase − 1 − |out|` spells `unaryField |out| ++ encodeGateRecordStream out`, the frontier
marker `fm = workBase + |encodeGateRecordStream out|` is just past the records, and there is room to
the left (`1 ≤ oc`), then after `emitTape` the window at `oc − 1` spells
`unaryField |out+1| ++ encodeGateRecordStream (out ++ [g])` — the invariant's output clause for the
emitted state. -/
theorem emitTape_output_window {n L : Nat} (tape : Fin L → Bool) (oc : Nat) (out : List (SLGate n))
    (g : SLGate n) (hoc : 1 ≤ oc)
    (hwin : windowSpells tape oc (unaryField out.length ++ encodeGateRecordStream out))
    (hfmrec : oc + (unaryField out.length ++ encodeGateRecordStream out).length
        = oc + out.length + 1 + (encodeGateRecordStream out).length)
    (hfit : oc + (unaryField out.length ++ encodeGateRecordStream out).length
        + (encodeGateRecord g).length < L) :
    windowSpells (emitTape tape (oc - 1 + 1)
        (oc + (unaryField out.length ++ encodeGateRecordStream out).length)
        (encodeGateRecord g))
      (oc - 1)
      (unaryField (out.length + 1) ++ encodeGateRecordStream (out ++ [g])) := by
  obtain ⟨hwfit, hwc⟩ := hwin
  -- Abbreviations and lengths.
  set body := unaryField out.length ++ encodeGateRecordStream out with hbody
  set fm := oc + body.length with hfm
  set rec := encodeGateRecord g with hrec
  have hbl : body.length = out.length + 1 + (encodeGateRecordStream out).length := by
    rw [hbody, List.length_append, unaryField_length]
  have hsucc : oc - 1 + 1 = oc := by omega
  rw [hsucc, gateStream_emit_eq, ← hbody, ← hrec]
  -- The target window: (true :: body) ++ rec, at base oc - 1.
  have hcl : ((true :: body) ++ rec).length = body.length + 1 + rec.length := by
    simp only [List.length_append, List.length_cons]
  refine ⟨?_, fun q hlo hhi => ?_⟩
  · rw [hcl]; omega
  · -- Cell value at q ∈ [oc-1, oc-1 + (1 + |body| + |rec|)).
    rw [hcl] at hhi
    unfold emitTape
    by_cases h0 : (q : Nat) = oc - 1
    · rw [if_pos (by omega), show (q : Nat) - (oc - 1) = 0 from by omega]
      rw [List.getD_append (true :: body) rec false 0 (by simp)]
      rfl
    · rw [if_neg (by omega)]
      by_cases h1 : fm ≤ (q : Nat) ∧ (q : Nat) < fm + rec.length
      · -- the new record
        rw [if_pos h1,
          List.getD_append_right (true :: body) rec false ((q : Nat) - (oc - 1))
            (by simp only [List.length_cons]; rw [hfm] at h1; omega)]
        congr 1
        simp only [List.length_cons]; rw [hfm] at h1 ⊢; omega
      · rw [if_neg h1]
        by_cases h2 : (q : Nat) = fm + rec.length
        · -- past the records: the window ends at fm + |rec|, excluded by hhi
          exfalso; rw [hfm] at h2; omega
        · rw [if_neg h2]
          -- inside body: transport from the old window.
          have hqbody : oc ≤ (q : Nat) ∧ (q : Nat) < oc + body.length := by
            rw [hfm] at h1 h2; omega
          rw [hwc q (by omega) (by omega)]
          have hidx : (q : Nat) - (oc - 1) = ((q : Nat) - oc) + 1 := by omega
          rw [hidx,
            List.getD_append (true :: body) rec false ((q : Nat) - oc + 1)
              (by simp only [List.length_cons]; omega),
            List.getD_cons_succ]

/-- After `emitTape`, the new frontier marker sits at `fm + |rec|`. -/
theorem emitTape_FM {L : Nat} (tape : Fin L → Bool) (oc fm : Nat) (rec : List Bool)
    (hfm : oc - 1 < fm) :
    ∀ q : Fin L, (q : Nat) = fm + rec.length → emitTape tape oc fm rec q = true := by
  intro q hq
  unfold emitTape
  rw [if_neg (by omega), if_neg (by omega), if_pos hq]

end ContractExpansion
end Frontier
end Pnp4
