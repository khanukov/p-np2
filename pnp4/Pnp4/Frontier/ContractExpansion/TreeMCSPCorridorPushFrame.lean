import Pnp4.Frontier.ContractExpansion.TreeMCSPCorridorRoutesBack
import Pnp4.Frontier.ContractExpansion.TreeMCSPWriteBits

/-!
# Corridor frame push — D2t-5b (Block A4a): appending a control frame at the zone's right end

The node arm pushes `(tag, tag.arity)` onto the control stack.  Under the corridor layout the stack
is right-anchored (`encodeCtrlStackR`, top rightmost), so the push is a **rightward append**: from the
first free cell past the content (`ctrlBase + |encodeCtrlStackR st.ctrl|`), `writeBits` lays down
`encodeCtrlFrameR (tag, tag.arity)`, and the grown window spells exactly
`encodeCtrlStackR ((tag, tag.arity) :: st.ctrl)` — the codec's push equation.

* `writeBits_appends_window` — the generic fact: a `writeBits` run at the right end of a spelled
  window grows it by the written bits (the old content is outside the write window, hence untouched).
* `corridor_push_ctrl_frame` — the instantiation against `driverCorridorInv`'s clauses (fits within
  the control zone's capacity given room for the frame).

**Progress classification (AGENTS.md): Infrastructure** — verifier machine run-throughs; build no
verifier and prove no separation.  Standard `[propext, Classical.choice, Quot.sound]` triple only.
**No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram
open Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-- **`writeBits` appends to a spelled window.**  If `[base, base + |xs|)` spells `xs` and the head
sits at `base + |xs|` (the first free cell), then after the `writeBits bs` run the window
`[base, base + |xs| + |bs|)` spells `xs ++ bs` — and every cell outside the write window keeps its
old value. -/
theorem writeBits_appends_window {L : Nat} (bs xs : List Bool) (base : Nat)
    (c : Configuration (M := (writeBits bs).toPhased.toTM) L)
    (hphase : (c.state.fst : Nat) = 0)
    (hhead : (c.head : Nat) = base + xs.length)
    (hroom : (c.head : Nat) + bs.length < (writeBits bs).toPhased.toTM.tapeLength L)
    (hwin : windowSpells c.tape base xs) :
    windowSpells (TM.runConfig (M := (writeBits bs).toPhased.toTM) c bs.length).tape base (xs ++ bs)
    ∧ ((TM.runConfig (M := (writeBits bs).toPhased.toTM) c bs.length).head : Nat)
        = base + xs.length + bs.length
    ∧ ∀ q : Fin ((writeBits bs).toPhased.toTM.tapeLength L),
        ((q : Nat) < base + xs.length ∨ base + xs.length + bs.length ≤ (q : Nat)) →
        (TM.runConfig (M := (writeBits bs).toPhased.toTM) c bs.length).tape q = c.tape q := by
  obtain ⟨hph, hhd, htp⟩ := writeBits_runConfig bs c hphase hroom
  obtain ⟨hfit, hcells⟩ := hwin
  refine ⟨⟨by rw [List.length_append]; omega, fun q hlo hhi => ?_⟩, by rw [hhd, hhead], fun q hq => ?_⟩
  · rw [htp q]
    simp only [List.length_append] at hhi
    by_cases hqw : (c.head : Nat) ≤ (q : Nat) ∧ (q : Nat) < (c.head : Nat) + bs.length
    · rw [if_pos hqw, List.getD_append_right _ _ _ _ (by omega)]
      congr 1
      omega
    · rw [if_neg hqw]
      have hql : (q : Nat) < base + xs.length := by omega
      rw [hcells q hlo hql, List.getD_append _ _ _ _ (by omega)]
  · rw [htp q, if_neg (by omega)]

/-- **The corridor control-frame push.**  From the first free cell past the control content, the
`writeBits (encodeCtrlFrameR (tag, tag.arity))` run grows the control window to spell the pushed
stack `encodeCtrlStackR ((tag, tag.arity) :: st.ctrl)`, leaves every cell outside the frame window
untouched, and parks the head on the cell just past the new content. -/
theorem corridor_push_ctrl_frame {n L : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (z : DriverCorridor) (st : DriveState n) (tag : ITag)
    (c : Configuration (M := (writeBits (encodeCtrlFrameR (tag, tag.arity))).toPhased.toTM) L)
    (hinv : driverCorridorInv width h_width z c.tape st)
    (hphase : (c.state.fst : Nat) = 0)
    (hhead : (c.head : Nat) = z.ctrlBase + (encodeCtrlStackR st.ctrl).length)
    (hcap : z.ctrlBase + (encodeCtrlStackR st.ctrl).length
        + (encodeCtrlFrameR (tag, tag.arity)).length ≤ z.ctrlEnd) :
    windowSpells (TM.runConfig
        (M := (writeBits (encodeCtrlFrameR (tag, tag.arity))).toPhased.toTM) c
        (encodeCtrlFrameR (tag, tag.arity)).length).tape
      z.ctrlBase (encodeCtrlStackR ((tag, tag.arity) :: st.ctrl))
    ∧ ((TM.runConfig (M := (writeBits (encodeCtrlFrameR (tag, tag.arity))).toPhased.toTM) c
        (encodeCtrlFrameR (tag, tag.arity)).length).head : Nat)
        = z.ctrlBase + (encodeCtrlStackR ((tag, tag.arity) :: st.ctrl)).length
    ∧ ∀ q : Fin ((writeBits (encodeCtrlFrameR (tag, tag.arity))).toPhased.toTM.tapeLength L),
        ((q : Nat) < z.ctrlBase + (encodeCtrlStackR st.ctrl).length
          ∨ z.ctrlBase + (encodeCtrlStackR ((tag, tag.arity) :: st.ctrl)).length ≤ (q : Nat)) →
        (TM.runConfig (M := (writeBits (encodeCtrlFrameR (tag, tag.arity))).toPhased.toTM) c
          (encodeCtrlFrameR (tag, tag.arity)).length).tape q = c.tape q := by
  obtain ⟨hwf, hcert, hcfit, hM, hczeros, hout, hofit, hFM, hffit, hfzeros, hval, hvfit, hvzeros,
    hshw, hsfit, hszeros, hctrl, hcfit2, hvalid, hcoh⟩ := hinv
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hwf
  have hlen : (encodeCtrlStackR ((tag, tag.arity) :: st.ctrl)).length
      = (encodeCtrlStackR st.ctrl).length + (encodeCtrlFrameR (tag, tag.arity)).length := by
    rw [encodeCtrlStackR_cons, List.length_append]
  obtain ⟨hw, hh, hu⟩ := writeBits_appends_window (encodeCtrlFrameR (tag, tag.arity))
    (encodeCtrlStackR st.ctrl) z.ctrlBase c hphase hhead
    (by
      have := hctrl.1
      omega)
    hctrl
  refine ⟨?_, ?_, ?_⟩
  · rw [encodeCtrlStackR_cons]
    exact hw
  · rw [hh, hlen]
    omega
  · intro q hq
    exact hu q (by rw [hlen] at hq; omega)

end ContractExpansion
end Frontier
end Pnp4
