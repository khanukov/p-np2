import Pnp4.Frontier.ContractExpansion.TreeMCSPDriveStepTerminates

/-!
# `reachable_outLen_le_size` — D2t-5b (Block A5d, part 1): the reachable WORK-length bound

The first of the **reachable-state bounds** that will discharge `DriverStepFits` (Block A5b) along the
driver run.  `DriverStepFits` requires, among other zone capacities, that the WORK output never
outgrows its zone; the foundation is that the abstract `out` list never gets longer than the final
flattened program `(flatten c).gates`, i.e. `c.size` gates.

`DriveState.step` only ever leaves `out` unchanged or appends one gate (`out ++ [g]`), so `out.length`
is **monotone non-decreasing** along the run (`outLen_step_le` / `outLen_iterate_mono`); combined with
the proven termination endpoint `driveStep_halts_bound` (after `3 · c.size` steps `out` is exactly
`(flatten c).gates`, length `c.size` by `CircuitTree.flatten_length`), every state reachable within the
run satisfies `out.length ≤ c.size`.

This is one ingredient of the eventual capacity discharge; the companion bounds (the operand /
record-size bounds via straight-line-program validity, and the value/control stack depth bounds) are
separate sub-bricks.

**Progress classification (AGENTS.md): Infrastructure** — a pure reachable-state bound on the verified
small-step driver; builds no machine and proves no separation.  Standard `[propext, Classical.choice,
Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-- One `DriveState.step` never shortens `out`: every branch leaves it unchanged or appends one gate. -/
theorem outLen_step_le {n : Nat} (s : DriveState n) : s.out.length ≤ s.step.out.length := by
  obtain ⟨toks, out, ctrl, val, settling⟩ := s
  cases settling with
  | true =>
      cases ctrl with
      | nil => simp [DriveState.step]
      | cons f ctrl' =>
          obtain ⟨tag, rem⟩ := f
          by_cases hrem : rem = 1
          · subst hrem
            cases tag with
            | tnot =>
                cases val with
                | nil => simp [DriveState.step]
                | cons i vs => simp [DriveState.step]
            | tand =>
                cases val with
                | nil => simp [DriveState.step]
                | cons i2 rest =>
                    cases rest with
                    | nil => simp [DriveState.step]
                    | cons i1 vs => simp [DriveState.step]
            | tor =>
                cases val with
                | nil => simp [DriveState.step]
                | cons i2 rest =>
                    cases rest with
                    | nil => simp [DriveState.step]
                    | cons i1 vs => simp [DriveState.step]
          · simp [DriveState.step, hrem]
  | false =>
      cases toks with
      | nil => simp [DriveState.step]
      | cons tok toks' =>
          cases tok with
          | leaf g => simp [DriveState.step]
          | node tag => simp [DriveState.step]

/-- `out.length` is monotone along the iterated run: from any start, after `d` more steps it is no
shorter. -/
theorem outLen_iterate_mono {n : Nat} (s0 : DriveState n) (a : Nat) :
    ∀ d, (DriveState.step^[a] s0).out.length ≤ (DriveState.step^[a + d] s0).out.length := by
  intro d
  induction d with
  | zero => simp
  | succ d ih =>
      have hstep : (DriveState.step^[a + d] s0).out.length
          ≤ (DriveState.step^[a + (d + 1)] s0).out.length := by
        rw [show a + (d + 1) = (a + d) + 1 from by omega, Function.iterate_succ_apply']
        exact outLen_step_le _
      exact le_trans ih hstep

/-- Monotonicity in the step index: `a ≤ b → out_a.length ≤ out_b.length`. -/
theorem outLen_iterate_mono_le {n : Nat} (s0 : DriveState n) {a b : Nat} (hab : a ≤ b) :
    (DriveState.step^[a] s0).out.length ≤ (DriveState.step^[b] s0).out.length := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  exact outLen_iterate_mono s0 a d

/-- **The reachable WORK-length bound.**  Every state reachable within the driver run for `c`
(`j ≤ 3 · c.size` micro-steps from the empty start) has `out.length ≤ c.size` — `out` never outgrows
the final flattened program.  Combines `out`-monotonicity with the termination endpoint
`driveStep_halts_bound` (final `out = (flatten c).gates`, length `c.size`). -/
theorem reachable_outLen_le_size {n : Nat} (c : CircuitTree n) {j : Nat} (hj : j ≤ 3 * c.size) :
    (DriveState.step^[j] (⟨preorder c, [], [], [], false⟩ : DriveState n)).out.length ≤ c.size := by
  have hmono := outLen_iterate_mono_le (⟨preorder c, [], [], [], false⟩ : DriveState n) hj
  obtain ⟨_, hout⟩ := driveStep_halts_bound c
  rw [hout, CircuitTree.flatten_length] at hmono
  exact hmono

/-! ### Value-stack entry bound

Every index on the value stack is a WORK position of an already-emitted gate, hence `< out.length`.
This is a clean step-invariant (each push deposits the just-emitted gate's index `out.length`, which is
`< out.length + 1`, the new length; surviving entries were already below the old, smaller length), and
combined with the WORK-length bound it gives `v < c.size` for every reachable value entry — the bound
the right-anchored `encodeNatStackR` length and the operand back-references need. -/

/-- Invariant: every value-stack entry is a valid back-reference (`< out.length`). -/
def ValEntriesBounded {n : Nat} (s : DriveState n) : Prop :=
  ∀ v ∈ s.val, v < s.out.length

/-- The value-entry bound is preserved by one `DriveState.step`. -/
theorem valEntries_step {n : Nat} (s : DriveState n) (h : ValEntriesBounded s) :
    ValEntriesBounded s.step := by
  obtain ⟨toks, out, ctrl, val, settling⟩ := s
  simp only [ValEntriesBounded] at h ⊢
  -- The common push shape: new value stack `w :: tail` (`w = out.length`), new WORK `out ++ [g]`,
  -- with every old `tail` entry already bounded by `out.length`.
  have push : ∀ (g : SLGate n) (tail : List Nat),
      (∀ x ∈ tail, x < out.length) →
      ∀ y ∈ out.length :: tail, y < (out ++ [g]).length := by
    intro g tail htail y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · simp
    · have := htail y hy
      simp only [List.length_append, List.length_cons, List.length_nil]; omega
  cases settling with
  | true =>
      cases ctrl with
      | nil => simpa [DriveState.step] using h
      | cons f ctrl' =>
          obtain ⟨tag, rem⟩ := f
          by_cases hrem : rem = 1
          · subst hrem
            cases tag with
            | tnot =>
                cases val with
                | nil => simpa [DriveState.step] using h
                | cons i vs =>
                    show ∀ y ∈ out.length :: vs, y < (out ++ [SLGate.notGate i]).length
                    exact push _ vs (fun x hx => h x (List.mem_cons_of_mem i hx))
            | tand =>
                cases val with
                | nil => simpa [DriveState.step] using h
                | cons i2 rest =>
                    cases rest with
                    | nil => simpa [DriveState.step] using h
                    | cons i1 vs =>
                        show ∀ y ∈ out.length :: vs, y < (out ++ [SLGate.andGate i1 i2]).length
                        exact push _ vs
                          (fun x hx => h x (List.mem_cons_of_mem i2 (List.mem_cons_of_mem i1 hx)))
            | tor =>
                cases val with
                | nil => simpa [DriveState.step] using h
                | cons i2 rest =>
                    cases rest with
                    | nil => simpa [DriveState.step] using h
                    | cons i1 vs =>
                        show ∀ y ∈ out.length :: vs, y < (out ++ [SLGate.orGate i1 i2]).length
                        exact push _ vs
                          (fun x hx => h x (List.mem_cons_of_mem i2 (List.mem_cons_of_mem i1 hx)))
          · simpa [DriveState.step, hrem] using h
  | false =>
      cases toks with
      | nil => simpa [DriveState.step] using h
      | cons tok toks' =>
          cases tok with
          | leaf g =>
              show ∀ y ∈ out.length :: val, y < (out ++ [g]).length
              exact push g val h
          | node tag => simpa [DriveState.step] using h

/-- The value-entry bound holds at every iterate (it holds at the empty start and is step-preserved). -/
theorem valEntries_iterate {n : Nat} (s0 : DriveState n) (h0 : ValEntriesBounded s0) (j : Nat) :
    ValEntriesBounded (DriveState.step^[j] s0) := by
  induction j with
  | zero => simpa using h0
  | succ j ih => rw [Function.iterate_succ_apply']; exact valEntries_step _ ih

/-- **The reachable value-entry bound.**  Every value-stack index reachable within the driver run for
`c` (`j ≤ 3 · c.size` steps) is `< c.size` — a valid WORK back-reference into a program of `c.size`
gates.  (`v < out.length ≤ c.size` via `valEntries_iterate` and `reachable_outLen_le_size`.) -/
theorem reachable_valEntry_lt_size {n : Nat} (c : CircuitTree n) {j : Nat} (hj : j ≤ 3 * c.size)
    {v : Nat}
    (hv : v ∈ (DriveState.step^[j] (⟨preorder c, [], [], [], false⟩ : DriveState n)).val) :
    v < c.size := by
  have hbound := valEntries_iterate (⟨preorder c, [], [], [], false⟩ : DriveState n)
    (by intro w hw; simp at hw) j v hv
  have hout := reachable_outLen_le_size c hj
  omega

/-! ### Value-stack depth bound

The value stack never holds more entries than `out.length + 1`: a leaf read grows both by one, a
settle-emit pops `k ≥ 1` and pushes one (so the stack shrinks or stays while `out` grows), and the
other branches touch neither.  Combined with the WORK-length bound this gives `val.length ≤ c.size + 1`
— the stack-depth bound the right-anchored `encodeNatStackR` length needs. -/

/-- Invariant: the value stack is no deeper than `out.length + 1`. -/
def ValDepthBounded {n : Nat} (s : DriveState n) : Prop :=
  s.val.length ≤ s.out.length + 1

/-- The value-depth bound is preserved by one `DriveState.step`. -/
theorem valDepth_step {n : Nat} (s : DriveState n) (h : ValDepthBounded s) :
    ValDepthBounded s.step := by
  obtain ⟨toks, out, ctrl, val, settling⟩ := s
  simp only [ValDepthBounded] at h ⊢
  cases settling with
  | true =>
      cases ctrl with
      | nil => simpa [DriveState.step] using h
      | cons f ctrl' =>
          obtain ⟨tag, rem⟩ := f
          by_cases hrem : rem = 1
          · subst hrem
            cases tag with
            | tnot =>
                cases val with
                | nil => simpa [DriveState.step] using h
                | cons i vs =>
                    show (out.length :: vs).length ≤ (out ++ [SLGate.notGate i]).length + 1
                    simp only [List.length_cons, List.length_append, List.length_nil] at h ⊢
                    omega
            | tand =>
                cases val with
                | nil => simpa [DriveState.step] using h
                | cons i2 rest =>
                    cases rest with
                    | nil => simpa [DriveState.step] using h
                    | cons i1 vs =>
                        show (out.length :: vs).length ≤ (out ++ [SLGate.andGate i1 i2]).length + 1
                        simp only [List.length_cons, List.length_append, List.length_nil] at h ⊢
                        omega
            | tor =>
                cases val with
                | nil => simpa [DriveState.step] using h
                | cons i2 rest =>
                    cases rest with
                    | nil => simpa [DriveState.step] using h
                    | cons i1 vs =>
                        show (out.length :: vs).length ≤ (out ++ [SLGate.orGate i1 i2]).length + 1
                        simp only [List.length_cons, List.length_append, List.length_nil] at h ⊢
                        omega
          · simpa [DriveState.step, hrem] using h
  | false =>
      cases toks with
      | nil => simpa [DriveState.step] using h
      | cons tok toks' =>
          cases tok with
          | leaf g =>
              show (out.length :: val).length ≤ (out ++ [g]).length + 1
              simp only [List.length_cons, List.length_append, List.length_nil] at h ⊢
              omega
          | node tag => simpa [DriveState.step] using h

/-- The value-depth bound holds at every iterate (it holds at the empty start and is step-preserved). -/
theorem valDepth_iterate {n : Nat} (s0 : DriveState n) (h0 : ValDepthBounded s0) (j : Nat) :
    ValDepthBounded (DriveState.step^[j] s0) := by
  induction j with
  | zero => simpa using h0
  | succ j ih => rw [Function.iterate_succ_apply']; exact valDepth_step _ ih

/-- **The reachable value-depth bound.**  Every state reachable within the driver run for `c`
(`j ≤ 3 · c.size` steps) has `val.length ≤ c.size + 1` — combining the depth invariant
`val.length ≤ out.length + 1` with the WORK-length bound `out.length ≤ c.size`. -/
theorem reachable_valLen_le_size {n : Nat} (c : CircuitTree n) {j : Nat} (hj : j ≤ 3 * c.size) :
    (DriveState.step^[j] (⟨preorder c, [], [], [], false⟩ : DriveState n)).val.length
      ≤ c.size + 1 := by
  have hdepth := valDepth_iterate (⟨preorder c, [], [], [], false⟩ : DriveState n) (by simp [ValDepthBounded]) j
  have hout := reachable_outLen_le_size c hj
  simp only [ValDepthBounded] at hdepth
  omega

end ContractExpansion
end Frontier
end Pnp4
