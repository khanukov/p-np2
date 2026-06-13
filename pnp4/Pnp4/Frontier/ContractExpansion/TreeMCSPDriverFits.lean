import Pnp4.Frontier.ContractExpansion.TreeMCSPDriverTapes
import Pnp4.Frontier.ContractExpansion.TreeMCSPDriverReachBound

/-!
# `CorridorSized` — D2t-5b (Block A5d, completion): the capacity discharge

Discharges every `DriverStepFits` side condition (Block A5b) along the driver run, from **four
concrete zone-size inequalities** on the corridor (`CorridorSized`):

* the static count prefix pinned to the final gate count (`z.outCount = |(flatten c).gates|`);
* WORK room for the full final record stream `encodeGateRecordStream (flatten c).gates`;
* value room for `c.size + 1` entries of width `< c.size` each;
* control room for `c.size` frames of width `≤ 9` each (`rem ≤ 2`, `tagCode ≤ 2`).

The reachable-state bounds (`TreeMCSPDriverReachBound`) supply the per-state facts: WORK length and
record-stream length are monotone and pinned by the terminal `driveStep_halts_bound`; value entries /
depth and control frames / depth are step-invariants; a reachable `node` read always has a nonempty
tail (`preorder` ends with a leaf).  The capstone

`driverTapes_terminal_output_sized` — from the initial corridor layout, **with no per-step
hypotheses** (only `CorridorSized`), after `3 · c.size` micro-steps the output window spells
`encodeGateStream (flatten c).gates`.

This **completes Block A5d**: the semantic half of the A5 loop discharge now has no outstanding
side conditions beyond the corridor's polynomial sizing.

**Progress classification (AGENTS.md): Infrastructure** — capacity arithmetic over the verified
reachable-state bounds; builds no machine and proves no separation.  Standard `[propext,
Classical.choice, Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-! ### Record-stream length along the run -/

/-- One `DriveState.step` never shortens the encoded record stream. -/
theorem streamLen_step_le {n : Nat} (s : DriveState n) :
    (encodeGateRecordStream s.out).length ≤ (encodeGateRecordStream s.step.out).length := by
  rcases out_step_shape s with h | ⟨g, h⟩
  · rw [h]
  · rw [h, encodeGateRecordStream_snoc, List.length_append]
    omega

/-- Record-stream length is monotone along the iterated run. -/
theorem streamLen_iterate_mono {n : Nat} (s0 : DriveState n) (a : Nat) :
    ∀ d, (encodeGateRecordStream (DriveState.step^[a] s0).out).length
      ≤ (encodeGateRecordStream (DriveState.step^[a + d] s0).out).length := by
  intro d
  induction d with
  | zero => simp
  | succ d ih =>
      have hstep : (encodeGateRecordStream (DriveState.step^[a + d] s0).out).length
          ≤ (encodeGateRecordStream (DriveState.step^[a + (d + 1)] s0).out).length := by
        rw [show a + (d + 1) = (a + d) + 1 from by omega, Function.iterate_succ_apply']
        exact streamLen_step_le _
      exact le_trans ih hstep

/-- Record-stream length is monotone in the step index. -/
theorem streamLen_iterate_mono_le {n : Nat} (s0 : DriveState n) {a b : Nat} (hab : a ≤ b) :
    (encodeGateRecordStream (DriveState.step^[a] s0).out).length
      ≤ (encodeGateRecordStream (DriveState.step^[b] s0).out).length := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  exact streamLen_iterate_mono s0 a d

/-- **The reachable record-stream bound**: along the driver run for `c`, the encoded record stream
never outgrows the final one, `encodeGateRecordStream (flatten c).gates`. -/
theorem reachable_streamLen_le {n : Nat} (c : CircuitTree n) {j : Nat} (hj : j ≤ 3 * c.size) :
    (encodeGateRecordStream
        (DriveState.step^[j] (⟨preorder c, [], [], [], false⟩ : DriveState n)).out).length
      ≤ (encodeGateRecordStream (CircuitTree.flatten c).gates).length := by
  have hmono := streamLen_iterate_mono_le (⟨preorder c, [], [], [], false⟩ : DriveState n) hj
  obtain ⟨_, hout⟩ := driveStep_halts_bound c
  rw [hout] at hmono
  exact hmono

/-! ### Codec length bounds -/

/-- Tag codes are at most `2`. -/
theorem tagCode_le_two (tag : ITag) : tag.tagCode ≤ 2 := by
  cases tag <;> simp only [ITag.tagCode] <;> omega

/-- Arities are at most `2`. -/
theorem arity_le_two (tag : ITag) : tag.arity ≤ 2 := by
  cases tag <;> simp only [ITag.arity] <;> omega

/-- Mapped `(· + 3)` sum bound from an entry bound. -/
theorem map_add_three_sum_le (B : Nat) :
    ∀ S : List Nat, (∀ v ∈ S, v < B) → (S.map (· + 3)).sum ≤ S.length * (B + 2) := by
  intro S
  induction S with
  | nil => intro _; simp
  | cons v t ih =>
      intro hS
      have hv := hS v (List.mem_cons_self ..)
      have ht := ih (fun x hx => hS x (List.mem_cons_of_mem _ hx))
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have hexp : (t.length + 1) * (B + 2) = t.length * (B + 2) + (B + 2) := by ring
      omega

/-- The right-anchored value stack's width, from an entry bound. -/
theorem encodeNatStackR_length_le_of_lt (S : List Nat) (B : Nat) (hS : ∀ v ∈ S, v < B) :
    (encodeNatStackR S).length ≤ 1 + S.length * (B + 2) := by
  rw [encodeNatStackR_length]
  have := map_add_three_sum_le B S hS
  omega

/-- The right-anchored control stack's width, from the frame-count bound (`rem ≤ 2`): every frame
occupies at most `9` cells. -/
theorem encodeCtrlStackR_length_le (S : List (ITag × Nat)) (hS : ∀ f ∈ S, f.2 ≤ 2) :
    (encodeCtrlStackR S).length ≤ 1 + 9 * S.length := by
  induction S with
  | nil => simp
  | cons f t ih =>
      obtain ⟨tag, rem⟩ := f
      have hrem := hS (tag, rem) (List.mem_cons_self ..)
      have htag := tagCode_le_two tag
      have ht := ih (fun x hx => hS x (List.mem_cons_of_mem _ hx))
      rw [encodeCtrlStackR_cons, List.length_append, encodeCtrlFrameR_length]
      simp only [List.length_cons]
      simp only at hrem
      omega

/-! ### The sized corridor and the `DriverStepFits` discharge -/

/-- **The corridor sizing** for a certificate `c`: concrete zone-room inequalities covering every
reachable state's needs — output room for `c.size` gates, WORK room for the full final record
stream, value room for `c.size + 1` entries of width `< c.size`, shadow-count room for the full
unary count **plus the A5m-V fan-out scratch** (`2 · c.size + 3` cells past the base sentinel — the
value-push machine's restore loop works in `[shwBase, shwBase + 2·|out| + 3)`), control room for
`c.size` frames of width `≤ 9` plus one pushed frame. -/
def CorridorSized {n : Nat} (z : DriverCorridor) (c : CircuitTree n) : Prop :=
  z.outCount = (CircuitTree.flatten c).gates.length
  ∧ z.workBase + (encodeGateRecordStream (CircuitTree.flatten c).gates).length + 1 ≤ z.workEnd
  ∧ z.valBase + (1 + (c.size + 1) * (c.size + 2)) + (c.size + 3) ≤ z.valEnd
  ∧ z.shwBase + 2 * c.size + 3 ≤ z.shwEnd
  ∧ z.ctrlBase + (1 + 9 * c.size) + 9 ≤ z.ctrlEnd

/-- **The branch side conditions from state bounds.**  For any state whose components satisfy the
reachable bounds, the sized corridor discharges `DriverStepFits`. -/
theorem driverStepFits_of_bounds {n : Nat} (z : DriverCorridor) (c : CircuitTree n)
    (s : DriveState n) (hz : CorridorSized z c)
    (h1 : s.out.length ≤ c.size)
    (h2 : (encodeGateRecordStream s.step.out).length
        ≤ (encodeGateRecordStream (CircuitTree.flatten c).gates).length)
    (h3a : ∀ v ∈ s.val, v < c.size)
    (h3b : s.val.length ≤ c.size + 1)
    (h6 : ∀ (tag : ITag) (toks' : List (PreToken n)),
        s.toks = PreToken.node tag :: toks' → toks' ≠ [])
    (h4 : ∀ f ∈ s.ctrl, f.2 ≤ 2)
    (h5 : s.ctrl.length ≤ c.size) :
    DriverStepFits z s := by
  obtain ⟨_hzN, hzw, hzv, hzs, hzc⟩ := hz
  obtain ⟨toks, out, ctrl, val, settling⟩ := s
  dsimp only at h1 h3a h3b h4 h5
  cases settling with
  | true =>
      cases ctrl with
      | nil => simp only [DriverStepFits]
      | cons f ctrl' =>
          obtain ⟨tag, rem⟩ := f
          by_cases hrem : rem = 1
          · subst hrem
            cases tag with
            | tnot =>
                cases val with
                | nil => simp only [DriverStepFits, if_true]
                | cons i vs =>
                    have h2' : (encodeGateRecordStream
                        (out ++ [SLGate.notGate i])).length
                        ≤ (encodeGateRecordStream (CircuitTree.flatten c).gates).length := h2
                    rw [encodeGateRecordStream_snoc, List.length_append] at h2'
                    simp only [DriverStepFits, if_true]
                    refine ⟨by omega, ?_, by omega⟩
                    have henc := encodeNatStackR_length_le_of_lt vs c.size
                      (fun v hv => h3a v (List.mem_cons_of_mem _ hv))
                    have hlen : vs.length ≤ c.size + 1 := by
                      have := h3b
                      simp only [List.length_cons] at this
                      omega
                    have hmul : vs.length * (c.size + 2) ≤ (c.size + 1) * (c.size + 2) :=
                      Nat.mul_le_mul_right _ hlen
                    omega
            | tand =>
                cases val with
                | nil => simp only [DriverStepFits, if_true]
                | cons i2 rest =>
                    cases rest with
                    | nil => simp only [DriverStepFits, if_true]
                    | cons i1 vs =>
                        have h2' : (encodeGateRecordStream
                            (out ++ [SLGate.andGate i1 i2])).length
                            ≤ (encodeGateRecordStream
                                (CircuitTree.flatten c).gates).length := h2
                        rw [encodeGateRecordStream_snoc, List.length_append] at h2'
                        simp only [DriverStepFits, if_true]
                        refine ⟨by omega, ?_, by omega⟩
                        have henc := encodeNatStackR_length_le_of_lt vs c.size
                          (fun v hv => h3a v
                            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hv)))
                        have hlen : vs.length ≤ c.size + 1 := by
                          have := h3b
                          simp only [List.length_cons] at this
                          omega
                        have hmul : vs.length * (c.size + 2) ≤ (c.size + 1) * (c.size + 2) :=
                          Nat.mul_le_mul_right _ hlen
                        omega
            | tor =>
                cases val with
                | nil => simp only [DriverStepFits, if_true]
                | cons i2 rest =>
                    cases rest with
                    | nil => simp only [DriverStepFits, if_true]
                    | cons i1 vs =>
                        have h2' : (encodeGateRecordStream
                            (out ++ [SLGate.orGate i1 i2])).length
                            ≤ (encodeGateRecordStream
                                (CircuitTree.flatten c).gates).length := h2
                        rw [encodeGateRecordStream_snoc, List.length_append] at h2'
                        simp only [DriverStepFits, if_true]
                        refine ⟨by omega, ?_, by omega⟩
                        have henc := encodeNatStackR_length_le_of_lt vs c.size
                          (fun v hv => h3a v
                            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hv)))
                        have hlen : vs.length ≤ c.size + 1 := by
                          have := h3b
                          simp only [List.length_cons] at this
                          omega
                        have hmul : vs.length * (c.size + 2) ≤ (c.size + 1) * (c.size + 2) :=
                          Nat.mul_le_mul_right _ hlen
                        omega
          · show DriverStepFits z ⟨toks, out, (tag, rem) :: ctrl', val, true⟩
            simp only [DriverStepFits, if_neg hrem]
  | false =>
      cases toks with
      | nil => simp only [DriverStepFits]
      | cons tok toks' =>
          cases tok with
          | leaf g =>
              have h2' : (encodeGateRecordStream (out ++ [g])).length
                  ≤ (encodeGateRecordStream (CircuitTree.flatten c).gates).length := h2
              rw [encodeGateRecordStream_snoc, List.length_append] at h2'
              simp only [DriverStepFits]
              refine ⟨by omega, ?_, by omega⟩
              have henc := encodeNatStackR_length_le_of_lt val c.size h3a
              have hmul : val.length * (c.size + 2) ≤ (c.size + 1) * (c.size + 2) :=
                Nat.mul_le_mul_right _ h3b
              omega
          | node tag =>
              simp only [DriverStepFits]
              refine ⟨h6 tag toks' rfl, ?_⟩
              have henc := encodeCtrlStackR_length_le ctrl h4
              have harity := arity_le_two tag
              have htag := tagCode_le_two tag
              rw [encodeCtrlFrameR_length]
              omega

/-- **The reachable `DriverStepFits` discharge**: along the driver run for `c`, every step's side
conditions hold for a sized corridor. -/
theorem reachable_driverStepFits {n : Nat} (z : DriverCorridor) (c : CircuitTree n)
    (hz : CorridorSized z c) {j : Nat} (hj : j < 3 * c.size) :
    DriverStepFits z
      (DriveState.step^[j] (⟨preorder c, [], [], [], false⟩ : DriveState n)) := by
  refine driverStepFits_of_bounds z c _ hz
    (reachable_outLen_le_size c (by omega)) ?_
    (fun v hv => reachable_valEntry_lt_size c (by omega) hv)
    (reachable_valLen_le_size c (by omega))
    (fun tag toks' h => reachable_node_tail_ne_nil c j tag toks' h)
    (fun f hf => reachable_ctrlRem c j f hf)
    (reachable_ctrlLen_le_size c j)
  rw [show (DriveState.step^[j]
      (⟨preorder c, [], [], [], false⟩ : DriveState n)).step
    = DriveState.step^[j + 1] (⟨preorder c, [], [], [], false⟩ : DriveState n) from
    (Function.iterate_succ_apply' _ _ _).symm]
  exact reachable_streamLen_le c (by omega)

/-- **The transcoder's semantic endpoint, hypothesis-free** (Block A5d capstone).  From the initial
corridor layout for `c` on a **sized** corridor, after `3 · c.size` micro-steps the output window
spells `encodeGateStream (flatten c).gates` — no per-step side conditions remain. -/
theorem driverTapes_terminal_output_sized {n L : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (z : DriverCorridor) (c : CircuitTree n) (tape0 : Fin L → Bool)
    (hz : CorridorSized z c)
    (hinv0 : driverCorridorInv width h_width z tape0
      (⟨preorder c, [], [], [], false⟩ : DriveState n)) :
    windowSpells
      (driverTapes width h_width z (⟨preorder c, [], [], [], false⟩ : DriveState n) tape0
        (3 * c.size))
      (z.workBase - 1 - (CircuitTree.flatten c).gates.length)
      (encodeGateStream (CircuitTree.flatten c).gates) :=
  driverTapes_terminal_output width h_width z c tape0 hz.1 hinv0
    (fun _ hj => reachable_driverStepFits z c hz hj)

end ContractExpansion
end Frontier
end Pnp4
