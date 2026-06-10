import Pnp4.Frontier.ContractExpansion.TreeMCSPRegionScanSegments

/-!
# Region run transfer — D2t-5b (Block A5m-U4): whole native runs, transported to the host

The scan segments (U3) re-ran two components' inductions on the host.  The remaining components
(the binary→unary loop above all) have **long** native run proofs that must not be re-run.  This
module transports a whole native run into the host in one theorem:

* `TapeAgree` — the value-wise tape coupling between a host and a native configuration (the two
  machines' tape lengths differ; cells are matched by position value);
* `RegionEmbeddedMulti.run_track` — if the host couples to the native start (phase offset by
  `base`, equal head positions, agreeing tapes) and along the native run **(a)** no visited phase is
  redirect-mapped and **(b)** the head never reaches the native tape's last cell (no clamping), then
  after `t` steps host and native still couple: host phase = `base +` native phase, equal heads,
  agreeing tapes.

At assembly each component's safety conditions are discharged from its head/phase-bound lemmas, and
its native capstone then *is* the host-level run fact — no re-derivation.

**Progress classification (AGENTS.md): Infrastructure** — a generic simulation transfer; builds no
machine and proves no separation.  Standard `[propext, Classical.choice, Quot.sound]` triple only.
**No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-- Value-wise tape agreement between a host and a native configuration (cells matched by position
value; the two tape lengths differ). -/
def TapeAgree {U P : ConstStatePhasedProgram Unit} {L : Nat}
    (ch : Configuration (M := U.toPhased.toTM) L)
    (cn : Configuration (M := P.toPhased.toTM) L) : Prop :=
  ∀ (qh : Fin (U.toPhased.toTM.tapeLength L)) (qn : Fin (P.toPhased.toTM.tapeLength L)),
    (qh : Nat) = (qn : Nat) → ch.tape qh = cn.tape qn

namespace RegionEmbeddedMulti

variable {U P : ConstStatePhasedProgram Unit} {base : Nat} {redirect : Nat → Option Nat}

/-- **One coupled step.**  With the host at the (unmapped) offset phase, equal heads, and agreeing
tapes — and the native head clear of its tape's last cell — one step preserves the coupling. -/
theorem step_track (hUP : RegionEmbeddedMulti U P base redirect) {L : Nat}
    (hlen : P.toPhased.toTM.tapeLength L ≤ U.toPhased.toTM.tapeLength L)
    (ch : Configuration (M := U.toPhased.toTM) L) (cn : Configuration (M := P.toPhased.toTM) L)
    (hphase : (ch.state.fst : Nat) = base + (cn.state.fst : Nat))
    (hhead : (ch.head : Nat) = (cn.head : Nat))
    (htape : TapeAgree ch cn)
    (hred : redirect (cn.state.fst : Nat) = none)
    (hroom : (cn.head : Nat) + 1 < P.toPhased.toTM.tapeLength L) :
    ((TM.stepConfig (M := U.toPhased.toTM) ch).state.fst : Nat)
        = base + ((TM.stepConfig (M := P.toPhased.toTM) cn).state.fst : Nat)
      ∧ ((TM.stepConfig (M := U.toPhased.toTM) ch).head : Nat)
          = ((TM.stepConfig (M := P.toPhased.toTM) cn).head : Nat)
      ∧ TapeAgree (TM.stepConfig (M := U.toPhased.toTM) ch)
          (TM.stepConfig (M := P.toPhased.toTM) cn) := by
  -- The native phase, as a Fin of P.numPhases.
  have hnlt : (cn.state.fst : Nat) < P.numPhases := by
    have := cn.state.fst.isLt
    simpa [toPhased_numPhases] using this
  set j : Fin P.numPhases := ⟨(cn.state.fst : Nat), hnlt⟩ with hj
  -- The scanned bits agree.
  have hbit : ch.tape ch.head = cn.tape cn.head := htape ch.head cn.head hhead
  -- Native single-step facts (the standard recipe, on P's own machine).
  have hnphase : ((TM.stepConfig (M := P.toPhased.toTM) cn).state.fst : Nat)
      = (P.transition j () (cn.tape cn.head)).fst.val := by
    unfold TM.stepConfig
    rw [show cn.state = ⟨cn.state.fst, cn.state.snd⟩ from rfl]
    simp only [PhasedProgram.toTM_step]
    simp only [ConstStatePhasedProgram.toPhased]
    rfl
  have hnhead : (TM.stepConfig (M := P.toPhased.toTM) cn).head
      = cn.moveHead (P.transition j () (cn.tape cn.head)).snd.snd.snd := by
    unfold TM.stepConfig
    rw [show cn.state = ⟨cn.state.fst, cn.state.snd⟩ from rfl]
    simp only [PhasedProgram.toTM_step]
    simp only [ConstStatePhasedProgram.toPhased]
    rfl
  have hntape : (TM.stepConfig (M := P.toPhased.toTM) cn).tape
      = cn.write cn.head (P.transition j () (cn.tape cn.head)).snd.snd.fst := by
    unfold TM.stepConfig
    rw [show cn.state = ⟨cn.state.fst, cn.state.snd⟩ from rfl]
    simp only [PhasedProgram.toTM_step]
    simp only [ConstStatePhasedProgram.toPhased]
    rfl
  -- Host single-step facts via the region contract (the host bit is the native bit).
  have hijval : (ch.state.fst : Nat) = base + j.val := by simpa [hj] using hphase
  have hredj : redirect j.val = none := by simpa [hj] using hred
  have hhphase := hUP.stepConfig_normal_phase ch rfl j hijval hredj
  have hhhead := hUP.stepConfig_normal_head ch rfl j hijval hredj
  have hhtape := hUP.stepConfig_normal_tape ch rfl j hijval hredj
  rw [hbit] at hhphase hhhead hhtape
  refine ⟨?_, ?_, ?_⟩
  · rw [hhphase, hnphase]
  · rw [hhhead, hnhead]
    -- Equal heads move equally (the native never clamps; the host has at least as much room).
    cases hmv : (P.transition j () (cn.tape cn.head)).snd.snd.snd with
    | left =>
        by_cases h0 : (cn.head : Nat) = 0
        · simp only [Configuration.moveHead, dif_pos (hhead.trans h0), dif_pos h0]
          rw [hhead.trans h0, h0]
        · simp only [Configuration.moveHead, dif_neg (fun hc => h0 (hhead.symm.trans hc)),
            dif_neg h0]
          omega
    | right =>
        have hhroom : (ch.head : Nat) + 1 < U.toPhased.toTM.tapeLength L := by omega
        simp only [Configuration.moveHead, dif_pos (by omega : (cn.head : Nat) + 1
            < P.toPhased.toTM.tapeLength L), dif_pos hhroom]
        omega
    | stay =>
        simp only [Configuration.moveHead]
        exact hhead
  · intro qh qn hq
    rw [hhtape, hntape]
    by_cases hqh : qh = ch.head
    · have hqn : qn = cn.head := Fin.ext (by omega)
      subst hqh; subst hqn
      simp [Configuration.write]
    · have hqn : qn ≠ cn.head := by
        intro hc; subst hc
        exact hqh (Fin.ext (by omega))
      simp only [Configuration.write]
      rw [dif_neg hqh, dif_neg hqn]
      exact htape qh qn hq

/-- **Whole-run transfer.**  If the host couples to the native start, and along the native run no
visited phase is redirect-mapped and the head stays clear of the native tape's last cell, the
coupling persists for `t` steps: host phase = `base +` native phase, equal heads, agreeing tapes. -/
theorem run_track (hUP : RegionEmbeddedMulti U P base redirect) {L : Nat}
    (hlen : P.toPhased.toTM.tapeLength L ≤ U.toPhased.toTM.tapeLength L)
    (ch0 : Configuration (M := U.toPhased.toTM) L) (cn0 : Configuration (M := P.toPhased.toTM) L)
    (hphase0 : (ch0.state.fst : Nat) = base + (cn0.state.fst : Nat))
    (hhead0 : (ch0.head : Nat) = (cn0.head : Nat))
    (htape0 : TapeAgree ch0 cn0)
    (t : Nat)
    (hsafe : ∀ s, s < t →
      redirect (((TM.runConfig (M := P.toPhased.toTM) cn0 s).state.fst : Nat)) = none
      ∧ ((TM.runConfig (M := P.toPhased.toTM) cn0 s).head : Nat) + 1
          < P.toPhased.toTM.tapeLength L) :
    ((TM.runConfig (M := U.toPhased.toTM) ch0 t).state.fst : Nat)
        = base + ((TM.runConfig (M := P.toPhased.toTM) cn0 t).state.fst : Nat)
      ∧ ((TM.runConfig (M := U.toPhased.toTM) ch0 t).head : Nat)
          = ((TM.runConfig (M := P.toPhased.toTM) cn0 t).head : Nat)
      ∧ TapeAgree (TM.runConfig (M := U.toPhased.toTM) ch0 t)
          (TM.runConfig (M := P.toPhased.toTM) cn0 t) := by
  induction t with
  | zero => exact ⟨hphase0, hhead0, htape0⟩
  | succ t ih =>
      obtain ⟨hph, hhd, htp⟩ := ih (fun s hs => hsafe s (by omega))
      obtain ⟨hred, hroom⟩ := hsafe t (by omega)
      rw [TM.runConfig_succ, TM.runConfig_succ]
      exact step_track hUP hlen _ _ hph hhd htp hred hroom

end RegionEmbeddedMulti

end ContractExpansion
end Frontier
end Pnp4
