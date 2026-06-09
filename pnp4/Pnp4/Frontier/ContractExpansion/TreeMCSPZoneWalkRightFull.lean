import Pnp4.Frontier.ContractExpansion.TreeMCSPZoneWalkRightRun
import Pnp4.Frontier.ContractExpansion.TreeMCSPZoneWalkFull

/-!
# `zoneWalkRight` full traversal — D2t-5b (Block A4w): the rightward multi-block walk

The rightward mirror of `zoneWalkLeft_runConfig_walkZone`: from the **base sentinel** of a corridor
stack zone, `zoneWalkRight` crosses every block and stops, done, on the **second dead cell** past the
zone's content — in exactly `Σ (kᵢ + 2) + 3` steps, tape unchanged.

Structure: the φ2-anchored **inner traversal** works over the *bottom-first* spelled form
`innerSpell bs = flatMap (1^k ++ [0]) bs` (each block's ones then its trailing delimiter/dead cell);
the bridging identity `walkZone ks ++ [0] = [1, 0] ++ innerSpell ks.reverse` re-anchors it to the
zone codec, and the 2-step entry plus the 1-step exit close the ends.

**Progress classification (AGENTS.md): Infrastructure** — a verifier machine run-through; builds no
verifier and proves no separation.  Standard `[propext, Classical.choice, Quot.sound]` triple only.
**No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-- The bottom-first inner spelling: each block's ones, then its trailing `0` (for the last block that
`0` is the zone's first dead cell). -/
def innerSpell (bs : List Nat) : List Bool :=
  bs.flatMap (fun k => List.replicate k true ++ [false])

@[simp] theorem innerSpell_nil : innerSpell [] = [] := rfl

@[simp] theorem innerSpell_cons (k : Nat) (bs : List Nat) :
    innerSpell (k :: bs) = (List.replicate k true ++ [false]) ++ innerSpell bs := by
  unfold innerSpell
  rw [List.flatMap_cons]

theorem innerSpell_length (bs : List Nat) :
    (innerSpell bs).length = (bs.map (· + 1)).sum := by
  induction bs with
  | nil => rfl
  | cons k bs ih => rw [innerSpell_cons]; simp [ih]; omega

/-- **The bridging identity**: a zone codec extended by its first dead cell is the sentinel, the
first delimiter, and the bottom-first inner spelling. -/
theorem walkZone_append_false (ks : List Nat) :
    walkZone ks ++ [false] = true :: false :: innerSpell ks.reverse := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
      rw [walkZone_cons, List.append_assoc, List.reverse_cons]
      have : innerSpell (ks.reverse ++ [k])
          = innerSpell ks.reverse ++ (List.replicate k true ++ [false]) := by
        unfold innerSpell
        rw [List.flatMap_append]
        simp
      rw [this, show (false :: List.replicate k true) ++ [false]
          = (false :: (List.replicate k true ++ [false])) from by simp]
      rw [show (true :: false :: (innerSpell ks.reverse ++ (List.replicate k true ++ [false])))
          = (true :: false :: innerSpell ks.reverse) ++ (List.replicate k true ++ [false]) from by
        simp]
      rw [← ih]
      simp

/-- The inner step budget: `k + 2` per block plus the final exit step. -/
def innerSteps (bs : List Nat) : Nat :=
  (bs.map (· + 2)).sum + 1

@[simp] theorem innerSteps_nil : innerSteps [] = 1 := rfl

theorem innerSteps_cons (k : Nat) (bs : List Nat) :
    innerSteps (k :: bs) = (k + 2) + innerSteps bs := by
  unfold innerSteps
  simp
  omega

/-- **The inner traversal.**  From φ2 on the first cell of `innerSpell bs` (every block `≥ 2`), with
the cell just past it dead and on the tape, after `innerSteps bs` steps the walker is done (φ4) on
that cell, tape unchanged. -/
theorem zoneWalkRight_runConfig_inner {L : Nat}
    (c0 : Configuration (M := zoneWalkRight.toPhased.toTM) L) :
    ∀ (bs : List Nat), (∀ k ∈ bs, 2 ≤ k) →
      (c0.state.fst : Nat) = 2 →
      (c0.head : Nat) + (innerSpell bs).length < zoneWalkRight.toPhased.toTM.tapeLength L →
      windowSpells c0.tape (c0.head : Nat) (innerSpell bs) →
      (∀ p : Fin (zoneWalkRight.toPhased.toTM.tapeLength L),
        (p : Nat) = (c0.head : Nat) + (innerSpell bs).length → c0.tape p = false) →
      (((TM.runConfig (M := zoneWalkRight.toPhased.toTM) c0 (innerSteps bs)).state).fst : Nat) = 4
      ∧ ((TM.runConfig (M := zoneWalkRight.toPhased.toTM) c0 (innerSteps bs)).head : Nat)
          = (c0.head : Nat) + (innerSpell bs).length
      ∧ (TM.runConfig (M := zoneWalkRight.toPhased.toTM) c0 (innerSteps bs)).tape = c0.tape := by
  intro bs
  induction bs generalizing c0 with
  | nil =>
      intro _ hphase hfit hwin hdead
      rw [innerSteps_nil]
      simp only [innerSpell_nil, List.length_nil, Nat.add_zero] at hdead ⊢
      obtain ⟨h1, h2, h3⟩ := zoneWalkRight_runConfig_exit c0 hphase
        (hdead c0.head rfl)
      exact ⟨h1, h2, h3⟩
  | cons k bs ih =>
      intro hge hphase hfit hwin hdead
      have hk : 2 ≤ k := hge k (List.mem_cons_self)
      rw [innerSpell_cons] at hwin hfit hdead
      rw [List.length_append, List.length_append, List.length_replicate,
        List.length_singleton] at hfit hdead
      -- The block's ones and delimiter, pointwise.
      have hwblk := windowSpells_append_left c0.tape (c0.head : Nat) _ _ hwin
      have hwrest := windowSpells_append_right c0.tape (c0.head : Nat) _ _ hwin
      rw [List.length_append, List.length_replicate, List.length_singleton] at hwrest
      obtain ⟨hbfit, hbcells⟩ := hwblk
      rw [List.length_append, List.length_replicate, List.length_singleton] at hbfit
      have hones : ∀ p : Fin (zoneWalkRight.toPhased.toTM.tapeLength L),
          (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + k → c0.tape p = true := by
        intro p hp1 hp2
        have := hbcells p (by omega) (by simp; omega)
        rw [this, List.getD_append _ _ _ _ (by simp; omega)]
        exact getD_replicate_of_lt true false (by omega)
      have hdelim : ∀ p : Fin (zoneWalkRight.toPhased.toTM.tapeLength L),
          (p : Nat) = (c0.head : Nat) + k → c0.tape p = false := by
        intro p hp
        have := hbcells p (by omega) (by simp; omega)
        rw [this, List.getD_append_right _ _ _ _ (by simp; omega)]
        simp [hp]
      -- The block pass, then the IH on the rest.
      obtain ⟨hps, hhs, hts⟩ := zoneWalkRight_runConfig_block_segment c0 hphase k (by omega)
        (by omega) hones hdelim
      rw [innerSteps_cons, TM.runConfig_add]
      set c1 := TM.runConfig (M := zoneWalkRight.toPhased.toTM) c0 (k + 2) with hc1
      have hh1 : (c1.head : Nat) = (c0.head : Nat) + k + 1 := by rw [hc1, hhs]
      have hwin1 : windowSpells c1.tape (c1.head : Nat) (innerSpell bs) := by
        rw [hc1, hts]
        rw [hh1]
        exact hwrest
      have hfit1 : (c1.head : Nat) + (innerSpell bs).length
          < zoneWalkRight.toPhased.toTM.tapeLength L := by
        rw [hh1]; omega
      have hdead1 : ∀ p : Fin (zoneWalkRight.toPhased.toTM.tapeLength L),
          (p : Nat) = (c1.head : Nat) + (innerSpell bs).length → c1.tape p = false := by
        intro p hp
        rw [hc1, hts]
        exact hdead p (by rw [hh1] at hp; omega)
      obtain ⟨hf1, hf2, hf3⟩ := ih c1 (fun x hx => hge x (List.mem_cons_of_mem _ hx))
        hps hfit1 hwin1 hdead1
      refine ⟨hf1, ?_, ?_⟩
      · rw [hf2, hh1, innerSpell_cons, List.length_append, List.length_append,
          List.length_replicate, List.length_singleton]
        omega
      · rw [hf3, hc1]; exact hts

/-- Extending a spelled window by one pinned dead cell. -/
theorem windowSpells_snoc_false {L : Nat} (tape : Fin L → Bool) (base : Nat) (bits : List Bool)
    (h : windowSpells tape base bits)
    (hfit : base + bits.length < L)
    (hdead : ∀ p : Fin L, (p : Nat) = base + bits.length → tape p = false) :
    windowSpells tape base (bits ++ [false]) := by
  obtain ⟨hf, hc⟩ := h
  refine ⟨by simp; omega, fun q hlo hhi => ?_⟩
  simp only [List.length_append, List.length_singleton] at hhi
  by_cases hq : (q : Nat) < base + bits.length
  · rw [hc q hlo hq, List.getD_append _ _ _ _ (by omega)]
  · have hq' : (q : Nat) = base + bits.length := by omega
    rw [hdead q hq', List.getD_append_right _ _ _ _ (by omega)]
    simp [hq']

/-- The full rightward walk step budget: `k + 2` per block plus the entry (2) and exit (1). -/
def walkZoneStepsR (ks : List Nat) : Nat :=
  (ks.map (· + 2)).sum + 3

theorem walkZoneStepsR_eq (ks : List Nat) : walkZoneStepsR ks = 2 + innerSteps ks.reverse := by
  unfold walkZoneStepsR innerSteps
  rw [List.map_reverse, List.sum_reverse]
  omega

/-- **The full rightward traversal.**  From φ0 on the base sentinel of a zone spelling `walkZone ks`
(every block `≥ 2`), with the **two** dead cells just past the content pinned to `0`, after
`walkZoneStepsR ks` steps the walker is done (φ4) on the second dead cell
(`base + |walkZone ks| + 1`), tape unchanged. -/
theorem zoneWalkRight_runConfig_walkZone {L : Nat}
    (c0 : Configuration (M := zoneWalkRight.toPhased.toTM) L)
    (ks : List Nat) (hge : ∀ k ∈ ks, 2 ≤ k) (base : Nat)
    (hphase : (c0.state.fst : Nat) = 0)
    (hhead : (c0.head : Nat) = base)
    (hfit : base + (walkZone ks).length + 1 < zoneWalkRight.toPhased.toTM.tapeLength L)
    (hwin : windowSpells c0.tape base (walkZone ks))
    (hdead1 : ∀ p : Fin (zoneWalkRight.toPhased.toTM.tapeLength L),
      (p : Nat) = base + (walkZone ks).length → c0.tape p = false)
    (hdead2 : ∀ p : Fin (zoneWalkRight.toPhased.toTM.tapeLength L),
      (p : Nat) = base + (walkZone ks).length + 1 → c0.tape p = false) :
    (((TM.runConfig (M := zoneWalkRight.toPhased.toTM) c0 (walkZoneStepsR ks)).state).fst : Nat) = 4
    ∧ ((TM.runConfig (M := zoneWalkRight.toPhased.toTM) c0 (walkZoneStepsR ks)).head : Nat)
        = base + (walkZone ks).length + 1
    ∧ (TM.runConfig (M := zoneWalkRight.toPhased.toTM) c0 (walkZoneStepsR ks)).tape = c0.tape := by
  -- Extend the window by the first dead cell and re-anchor it bottom-first.
  have hwin' := windowSpells_snoc_false c0.tape base (walkZone ks) hwin (by omega) hdead1
  rw [walkZone_append_false] at hwin'
  have hlen : (walkZone ks).length = (innerSpell ks.reverse).length + 1 := by
    have := congrArg List.length (walkZone_append_false ks)
    simp at this
    omega
  -- The cell after the sentinel is the first delimiter/dead `0`.
  have hcell1 : ∀ p : Fin (zoneWalkRight.toPhased.toTM.tapeLength L),
      (p : Nat) = base + 1 → c0.tape p = false := by
    intro p hp
    obtain ⟨hf, hc⟩ := hwin'
    have := hc p (by omega) (by simp; omega)
    rw [this]
    have hidx : (p : Nat) - base = 1 := by omega
    rw [hidx]
    rfl
  -- The inner window, anchored at `base + 2`.
  have hwinInner : windowSpells c0.tape (base + 2) (innerSpell ks.reverse) := by
    have := windowSpells_append_right c0.tape base [true, false] (innerSpell ks.reverse)
      (by simpa using hwin')
    simpa using this
  -- Entry: 2 steps to φ2 on `base + 2`.
  obtain ⟨heph, hehd, hetp⟩ := zoneWalkRight_runConfig_entry c0 hphase
    (by omega) (fun p hp => hcell1 p (by omega))
  rw [walkZoneStepsR_eq, TM.runConfig_add]
  set c1 := TM.runConfig (M := zoneWalkRight.toPhased.toTM) c0 2 with hc1
  have hh1 : (c1.head : Nat) = base + 2 := by rw [hc1, hehd, hhead]
  -- Inner traversal from `base + 2`.
  obtain ⟨hf1, hf2, hf3⟩ := zoneWalkRight_runConfig_inner c1 ks.reverse
    (fun k hk => hge k (List.mem_reverse.mp hk))
    heph
    (by rw [hh1]; omega)
    (by rw [hc1, hetp, hh1]; exact hwinInner)
    (by
      intro p hp
      rw [hc1, hetp]
      exact hdead2 p (by rw [hh1] at hp; omega))
  refine ⟨hf1, ?_, ?_⟩
  · rw [hf2, hh1]; omega
  · rw [hf3, hc1]; exact hetp

end ContractExpansion
end Frontier
end Pnp4
