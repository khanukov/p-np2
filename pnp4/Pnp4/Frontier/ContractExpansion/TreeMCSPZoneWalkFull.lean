import Pnp4.Frontier.ContractExpansion.TreeMCSPZoneWalkRun

/-!
# `zoneWalkLeft` full-zone walk — D2t-5b (Block A4w): the multi-block traversal

The headline of the A4w walker line: from the rightmost content cell of a corridor stack zone,
`zoneWalkLeft` traverses **every** block and stops, done, on the dead `0` just left of the base
sentinel — in exactly `Σ (kᵢ + 3) + 2` steps, tape unchanged.

The zone is abstracted as a **block list** `ks` (top-first; each block `≥ 2` ones — the corridor
discipline): on tape it spells `walkZone ks = [1] ++ flatMap (fun k => [0] ++ 1^k) ks.reverse`
(sentinel at `base`, blocks bottom-to-top left-to-right).  Both corridor codecs are instances:
`encodeNatStackR S` is `walkZone (S.map (· + 2))` and `encodeCtrlStackR S` is
`walkZone (S.flatMap fun (tag, rem) => [tag.tagCode + 2, rem + 1])` — proven here as the two
instantiation equations, so the walk lemma applies to both stacks directly.

Proof: induction on `ks`, stitching `zoneWalkLeft_runConfig_field_segment` (the top block's pass,
`k + 3` steps, lands at φ0 on the next block's rightmost cell) and
`zoneWalkLeft_runConfig_sentinel` (the base case, `2` steps) through `TM.runConfig_add`, with the
pointwise tape facts extracted from the `windowSpells` hypothesis.

**Progress classification (AGENTS.md): Infrastructure** — a verifier machine run-through; builds no
verifier and proves no separation.  Standard `[propext, Classical.choice, Quot.sound]` triple only.
**No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram
open Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-- A corridor zone as the walker sees it: the base sentinel `1`, then the blocks bottom-to-top
left-to-right (`ks` lists them **top-first**), each block `[0] ++ 1^k`. -/
def walkZone (ks : List Nat) : List Bool :=
  true :: ks.reverse.flatMap (fun k => false :: List.replicate k true)

@[simp] theorem walkZone_nil : walkZone [] = [true] := rfl

@[simp] theorem walkZone_cons (k : Nat) (ks : List Nat) :
    walkZone (k :: ks) = walkZone ks ++ (false :: List.replicate k true) := by
  unfold walkZone
  rw [List.reverse_cons, List.flatMap_append]
  simp

theorem walkZone_length (ks : List Nat) :
    (walkZone ks).length = 1 + (ks.map (· + 1)).sum := by
  induction ks with
  | nil => rfl
  | cons k ks ih => rw [walkZone_cons]; simp [ih]; omega

/-- The value stack is a walk zone: blocks `v + 2`, top-first. -/
theorem encodeNatStackR_eq_walkZone (S : List Nat) :
    encodeNatStackR S = walkZone (S.map (· + 2)) := by
  induction S with
  | nil => rfl
  | cons v rest ih =>
      rw [encodeNatStackR_cons, ih, List.map_cons, walkZone_cons]
      rfl

/-- The control stack is a walk zone: each frame contributes the blocks `[tagCode + 2, rem + 1]`
(top-first: the tag block is rightmost). -/
theorem encodeCtrlStackR_eq_walkZone (S : List (ITag × Nat)) :
    encodeCtrlStackR S
      = walkZone (S.flatMap fun f => [f.1.tagCode + 2, f.2 + 1]) := by
  induction S with
  | nil => rfl
  | cons f rest ih =>
      obtain ⟨tag, rem⟩ := f
      rw [encodeCtrlStackR_cons, ih, List.flatMap_cons]
      simp only [List.cons_append, List.nil_append]
      rw [walkZone_cons, walkZone_cons]
      show _ ++ encodeCtrlFrameR (tag, rem) = _
      rw [encodeCtrlFrameR]
      simp [List.append_assoc]

/-- The walker's step budget for a zone: `k + 3` per block plus the `2`-step sentinel finish. -/
def walkZoneSteps (ks : List Nat) : Nat :=
  (ks.map (· + 3)).sum + 2

@[simp] theorem walkZoneSteps_nil : walkZoneSteps [] = 2 := rfl

theorem walkZoneSteps_cons (k : Nat) (ks : List Nat) :
    walkZoneSteps (k :: ks) = (k + 3) + walkZoneSteps ks := by
  unfold walkZoneSteps
  simp
  omega

/-- `getD` of a long-enough `replicate` is its element. -/
theorem getD_replicate_of_lt {α : Type _} (a d : α) {i n : Nat} (h : i < n) :
    (List.replicate n a).getD i d = a := by
  simp [List.getD, h]

/-- **The full-zone walk.**  If the window `[base, base + |walkZone ks|)` spells `walkZone ks` (every
block `≥ 2` ones), the cell `base − 1` is the dead `0` (and `1 ≤ base`), and the walker starts at φ0 on
the zone's rightmost content cell, then after `walkZoneSteps ks` steps it is **done** (φ4) with the
head on `base − 1`, tape unchanged. -/
theorem zoneWalkLeft_runConfig_walkZone {L : Nat}
    (c0 : Configuration (M := zoneWalkLeft.toPhased.toTM) L) :
    ∀ (ks : List Nat), (∀ k ∈ ks, 2 ≤ k) → ∀ (base : Nat), 1 ≤ base →
      (c0.state.fst : Nat) = 0 →
      (c0.head : Nat) = base + (walkZone ks).length - 1 →
      windowSpells c0.tape base (walkZone ks) →
      (∀ p : Fin (zoneWalkLeft.toPhased.toTM.tapeLength L),
        (p : Nat) = base - 1 → c0.tape p = false) →
      (((TM.runConfig (M := zoneWalkLeft.toPhased.toTM) c0 (walkZoneSteps ks)).state).fst : Nat) = 4
      ∧ ((TM.runConfig (M := zoneWalkLeft.toPhased.toTM) c0 (walkZoneSteps ks)).head : Nat)
          = base - 1
      ∧ (TM.runConfig (M := zoneWalkLeft.toPhased.toTM) c0 (walkZoneSteps ks)).tape = c0.tape := by
  intro ks
  induction ks generalizing c0 with
  | nil =>
      intro _ base hbase hphase hhead hwin hdead
      -- The zone is the bare sentinel at `base`; the head sits on it.
      have hh : (c0.head : Nat) = base := by
        simpa [walkZone_nil] using hhead
      rw [walkZoneSteps_nil]
      obtain ⟨h1, h2, h3⟩ := zoneWalkLeft_runConfig_sentinel c0 hphase (by omega)
        (fun p hp => hdead p (by omega))
      exact ⟨h1, by rw [h2, hh], h3⟩
  | cons k ks ih =>
      intro hge base hbase hphase hhead hwin hdead
      have hk : 2 ≤ k := hge k (List.mem_cons_self)
      -- Window split: the prefix `walkZone ks` at `base`, the top block `[0] ++ 1^k` after it.
      rw [walkZone_cons] at hwin hhead
      have hwpre := windowSpells_append_left c0.tape base _ _ hwin
      have hwblk := windowSpells_append_right c0.tape base _ _ hwin
      obtain ⟨hfit, hcells⟩ := hwblk
      rw [List.length_append] at hhead
      simp only [List.length_cons, List.length_replicate] at hhead hfit
      -- Head: on the top block's rightmost cell `base + |pre| + k`.
      have hH : (c0.head : Nat) = base + (walkZone ks).length + k := by omega
      -- The top block's ones and its delimiter, pointwise.
      have hones : ∀ p : Fin (zoneWalkLeft.toPhased.toTM.tapeLength L),
          (c0.head : Nat) - (k - 1) ≤ (p : Nat) → (p : Nat) ≤ (c0.head : Nat) - 1 →
          c0.tape p = true := by
        intro p hp1 hp2
        have hcell := hcells p (by omega) (by simp; omega)
        rw [hcell]
        have hd : (p : Nat) - (base + (walkZone ks).length)
            = ((p : Nat) - (base + (walkZone ks).length) - 1) + 1 := by omega
        rw [hd, List.getD_cons_succ]
        exact getD_replicate_of_lt true false (by omega)
      have hdelim : ∀ p : Fin (zoneWalkLeft.toPhased.toTM.tapeLength L),
          (p : Nat) = (c0.head : Nat) - (k - 1) - 1 → c0.tape p = false := by
        intro p hp
        have hcell := hcells p (by omega) (by simp; omega)
        rw [hcell]
        have hd : (p : Nat) - (base + (walkZone ks).length) = 0 := by omega
        rw [hd, List.getD_cons_zero]
      -- The top block's pass: k + 3 steps land at φ0 on the prefix zone's rightmost cell.
      obtain ⟨hps, hhs, hts⟩ := zoneWalkLeft_runConfig_field_segment c0 hphase (k - 1)
        (by omega) (by omega)
        (fun p hp1 hp2 => hones p hp1 hp2)
        (fun p hp => hdelim p hp)
      -- Stitch with the remaining walk via runConfig_add.
      rw [walkZoneSteps_cons, show k + 3 = (k - 1) + 4 by omega, TM.runConfig_add]
      set c1 := TM.runConfig (M := zoneWalkLeft.toPhased.toTM) c0 ((k - 1) + 4) with hc1
      have hh1 : (c1.head : Nat) = base + (walkZone ks).length - 1 := by
        rw [hc1, hhs]; omega
      have hwin1 : windowSpells c1.tape base (walkZone ks) := by
        rw [hc1, hts]; exact hwpre
      have hdead1 : ∀ p : Fin (zoneWalkLeft.toPhased.toTM.tapeLength L),
          (p : Nat) = base - 1 → c1.tape p = false := by
        intro p hp
        rw [hc1, hts]; exact hdead p hp
      obtain ⟨hf1, hf2, hf3⟩ :=
        ih c1 (fun k hk => hge k (List.mem_cons_of_mem _ hk)) base hbase hps hh1 hwin1 hdead1
      refine ⟨hf1, hf2, ?_⟩
      rw [hf3, hc1]
      exact hts

end ContractExpansion
end Frontier
end Pnp4
