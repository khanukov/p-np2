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

/-! ### The step's WORK shape

`out` either stays or grows by exactly one appended gate — the shape fact behind both length
monotonicities (`outLen_step_le` above and the record-stream length in the capacity discharge). -/

/-- One `DriveState.step` leaves `out` unchanged or appends exactly one gate. -/
theorem out_step_shape {n : Nat} (s : DriveState n) :
    s.step.out = s.out ∨ ∃ g : SLGate n, s.step.out = s.out ++ [g] := by
  obtain ⟨toks, out, ctrl, val, settling⟩ := s
  cases settling with
  | true =>
      cases ctrl with
      | nil => left; rfl
      | cons f ctrl' =>
          obtain ⟨tag, rem⟩ := f
          by_cases hrem : rem = 1
          · subst hrem
            cases tag with
            | tnot =>
                cases val with
                | nil => left; rfl
                | cons i vs => right; exact ⟨SLGate.notGate i, rfl⟩
            | tand =>
                cases val with
                | nil => left; rfl
                | cons i2 rest =>
                    cases rest with
                    | nil => left; rfl
                    | cons i1 vs => right; exact ⟨SLGate.andGate i1 i2, rfl⟩
            | tor =>
                cases val with
                | nil => left; rfl
                | cons i2 rest =>
                    cases rest with
                    | nil => left; rfl
                    | cons i1 vs => right; exact ⟨SLGate.orGate i1 i2, rfl⟩
          · left; simp [DriveState.step, hrem]
  | false =>
      cases toks with
      | nil => left; rfl
      | cons tok toks' =>
          cases tok with
          | leaf g => right; exact ⟨g, rfl⟩
          | node tag => left; rfl

/-! ### Control-stack bounds

Frames are pushed with `rem = arity ≤ 2` and only ever decremented, so every frame's remaining count
stays `≤ 2`; and a frame push consumes a token, so `ctrl.length + toks.length` never grows — giving
the reachable depth bound `ctrl.length ≤ c.size`. -/

/-- Invariant: every control frame's remaining count is at most `2` (the maximal arity). -/
def CtrlRemBounded {n : Nat} (s : DriveState n) : Prop :=
  ∀ f ∈ s.ctrl, f.2 ≤ 2

/-- The frame-count bound is preserved by one `DriveState.step`. -/
theorem ctrlRem_step {n : Nat} (s : DriveState n) (h : CtrlRemBounded s) :
    CtrlRemBounded s.step := by
  obtain ⟨toks, out, ctrl, val, settling⟩ := s
  simp only [CtrlRemBounded] at h ⊢
  cases settling with
  | true =>
      cases ctrl with
      | nil => simpa [DriveState.step] using h
      | cons f ctrl' =>
          obtain ⟨tag, rem⟩ := f
          by_cases hrem : rem = 1
          · subst hrem
            have htail : ∀ f ∈ ctrl', f.2 ≤ 2 := fun f hf => h f (List.mem_cons_of_mem _ hf)
            cases tag with
            | tnot =>
                cases val with
                | nil => simpa [DriveState.step] using h
                | cons i vs =>
                    show ∀ f ∈ ctrl', f.2 ≤ 2
                    exact htail
            | tand =>
                cases val with
                | nil => simpa [DriveState.step] using h
                | cons i2 rest =>
                    cases rest with
                    | nil => simpa [DriveState.step] using h
                    | cons i1 vs =>
                        show ∀ f ∈ ctrl', f.2 ≤ 2
                        exact htail
            | tor =>
                cases val with
                | nil => simpa [DriveState.step] using h
                | cons i2 rest =>
                    cases rest with
                    | nil => simpa [DriveState.step] using h
                    | cons i1 vs =>
                        show ∀ f ∈ ctrl', f.2 ≤ 2
                        exact htail
          · simp only [DriveState.step, if_neg hrem]
            intro f hf
            rcases List.mem_cons.mp hf with rfl | hf
            · have := h (tag, rem) (List.mem_cons_self ..)
              simp only at this ⊢
              omega
            · exact h f (List.mem_cons_of_mem _ hf)
  | false =>
      cases toks with
      | nil => simpa [DriveState.step] using h
      | cons tok toks' =>
          cases tok with
          | leaf g => simpa [DriveState.step] using h
          | node tag =>
              show ∀ f ∈ (tag, tag.arity) :: ctrl, f.2 ≤ 2
              intro f hf
              rcases List.mem_cons.mp hf with rfl | hf
              · simp only
                cases tag <;> simp [ITag.arity]
              · exact h f hf

/-- The frame-count bound holds at every iterate. -/
theorem ctrlRem_iterate {n : Nat} (s0 : DriveState n) (h0 : CtrlRemBounded s0) (j : Nat) :
    CtrlRemBounded (DriveState.step^[j] s0) := by
  induction j with
  | zero => simpa using h0
  | succ j ih => rw [Function.iterate_succ_apply']; exact ctrlRem_step _ ih

/-- **The reachable frame-count bound**: every control frame along the driver run has `rem ≤ 2`. -/
theorem reachable_ctrlRem {n : Nat} (c : CircuitTree n) (j : Nat) :
    CtrlRemBounded (DriveState.step^[j] (⟨preorder c, [], [], [], false⟩ : DriveState n)) :=
  ctrlRem_iterate _ (by intro f hf; simp at hf) j

/-- Invariant: control depth plus unread tokens never exceeds `B` (a push consumes a token). -/
def CtrlToksBounded {n : Nat} (B : Nat) (s : DriveState n) : Prop :=
  s.ctrl.length + s.toks.length ≤ B

/-- The depth-plus-tokens bound is preserved by one `DriveState.step`. -/
theorem ctrlToks_step {n : Nat} (B : Nat) (s : DriveState n) (h : CtrlToksBounded B s) :
    CtrlToksBounded B s.step := by
  obtain ⟨toks, out, ctrl, val, settling⟩ := s
  simp only [CtrlToksBounded] at h ⊢
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
                    show ctrl'.length + toks.length ≤ B
                    simp only [List.length_cons] at h
                    omega
            | tand =>
                cases val with
                | nil => simpa [DriveState.step] using h
                | cons i2 rest =>
                    cases rest with
                    | nil => simpa [DriveState.step] using h
                    | cons i1 vs =>
                        show ctrl'.length + toks.length ≤ B
                        simp only [List.length_cons] at h
                        omega
            | tor =>
                cases val with
                | nil => simpa [DriveState.step] using h
                | cons i2 rest =>
                    cases rest with
                    | nil => simpa [DriveState.step] using h
                    | cons i1 vs =>
                        show ctrl'.length + toks.length ≤ B
                        simp only [List.length_cons] at h
                        omega
          · simpa [DriveState.step, hrem] using h
  | false =>
      cases toks with
      | nil => simpa [DriveState.step] using h
      | cons tok toks' =>
          cases tok with
          | leaf g =>
              show ctrl.length + toks'.length ≤ B
              simp only [List.length_cons] at h
              omega
          | node tag =>
              show ((tag, tag.arity) :: ctrl).length + toks'.length ≤ B
              simp only [List.length_cons] at h ⊢
              omega

/-- The depth-plus-tokens bound holds at every iterate. -/
theorem ctrlToks_iterate {n : Nat} (B : Nat) (s0 : DriveState n) (h0 : CtrlToksBounded B s0)
    (j : Nat) : CtrlToksBounded B (DriveState.step^[j] s0) := by
  induction j with
  | zero => simpa using h0
  | succ j ih => rw [Function.iterate_succ_apply']; exact ctrlToks_step _ _ ih

/-- **The reachable control-depth bound**: along the driver run for `c`, the control stack never
holds more than `c.size` frames. -/
theorem reachable_ctrlLen_le_size {n : Nat} (c : CircuitTree n) (j : Nat) :
    (DriveState.step^[j] (⟨preorder c, [], [], [], false⟩ : DriveState n)).ctrl.length
      ≤ c.size := by
  have h := ctrlToks_iterate c.size (⟨preorder c, [], [], [], false⟩ : DriveState n)
    (by simp [CtrlToksBounded, preorder_length]) j
  simp only [CtrlToksBounded] at h
  omega

/-! ### The unread tokens form a suffix; preorder streams end with a leaf

`toks` only ever loses its head, so every reachable token list is a suffix of the initial preorder;
and a preorder serialisation always ends with a leaf token.  Together: a reachable state reading a
`node` token always has a nonempty tail — the shape fact the node branch of `DriverStepFits` needs. -/

/-- One `DriveState.step` keeps `toks` or drops its head — a suffix either way. -/
theorem toks_step_suffix {n : Nat} (s : DriveState n) : s.step.toks <:+ s.toks := by
  obtain ⟨toks, out, ctrl, val, settling⟩ := s
  cases settling with
  | true =>
      cases ctrl with
      | nil => exact List.suffix_refl _
      | cons f ctrl' =>
          obtain ⟨tag, rem⟩ := f
          by_cases hrem : rem = 1
          · subst hrem
            cases tag with
            | tnot =>
                cases val with
                | nil => exact List.suffix_refl _
                | cons i vs => exact List.suffix_refl _
            | tand =>
                cases val with
                | nil => exact List.suffix_refl _
                | cons i2 rest =>
                    cases rest with
                    | nil => exact List.suffix_refl _
                    | cons i1 vs => exact List.suffix_refl _
            | tor =>
                cases val with
                | nil => exact List.suffix_refl _
                | cons i2 rest =>
                    cases rest with
                    | nil => exact List.suffix_refl _
                    | cons i1 vs => exact List.suffix_refl _
          · simp only [DriveState.step, if_neg hrem]
            exact List.suffix_refl _
  | false =>
      cases toks with
      | nil => exact List.suffix_refl _
      | cons tok toks' =>
          cases tok with
          | leaf g => exact List.suffix_cons _ _
          | node tag => exact List.suffix_cons _ _

/-- The unread tokens at every iterate form a suffix of the initial token list. -/
theorem toks_iterate_suffix {n : Nat} (s0 : DriveState n) (j : Nat) :
    (DriveState.step^[j] s0).toks <:+ s0.toks := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact List.IsSuffix.trans (toks_step_suffix _) ih

/-- A preorder stream is never empty. -/
theorem preorder_ne_nil {n : Nat} (c : CircuitTree n) : preorder c ≠ [] := by
  cases c <;> simp [preorder]

/-- `getLast?` ignores a cons onto a nonempty list. -/
theorem getLast?_cons_of_ne_nil {α : Type _} (a : α) {l : List α} (h : l ≠ []) :
    (a :: l).getLast? = l.getLast? := by
  cases l with
  | nil => exact absurd rfl h
  | cons b t => exact List.getLast?_cons_cons ..

/-- `getLast?` ignores a prepended list when the right part is nonempty. -/
theorem getLast?_append_right_of_ne_nil {α : Type _} (l₁ : List α) {l₂ : List α} (h : l₂ ≠ []) :
    (l₁ ++ l₂).getLast? = l₂.getLast? := by
  induction l₁ with
  | nil => rfl
  | cons a t ih =>
      rw [List.cons_append,
        getLast?_cons_of_ne_nil a (fun hc => h (List.append_eq_nil_iff.mp hc).2), ih]

/-- **A preorder stream always ends with a leaf token** (the deepest-rightmost leaf). -/
theorem preorder_getLast_leaf {n : Nat} :
    ∀ c : CircuitTree n, ∃ g : SLGate n, (preorder c).getLast? = some (PreToken.leaf g) := by
  intro c
  induction c with
  | input i => exact ⟨SLGate.input i, rfl⟩
  | const b => exact ⟨SLGate.const b, rfl⟩
  | not c ih =>
      obtain ⟨g, hg⟩ := ih
      refine ⟨g, ?_⟩
      show (PreToken.node ITag.tnot :: preorder c).getLast? = some (PreToken.leaf g)
      rw [getLast?_cons_of_ne_nil _ (preorder_ne_nil c)]
      exact hg
  | and a b iha ihb =>
      obtain ⟨g, hg⟩ := ihb
      refine ⟨g, ?_⟩
      show (PreToken.node ITag.tand :: (preorder a ++ preorder b)).getLast?
        = some (PreToken.leaf g)
      rw [getLast?_cons_of_ne_nil _ (fun hc =>
          preorder_ne_nil b (List.append_eq_nil_iff.mp hc).2),
        getLast?_append_right_of_ne_nil _ (preorder_ne_nil b)]
      exact hg
  | or a b iha ihb =>
      obtain ⟨g, hg⟩ := ihb
      refine ⟨g, ?_⟩
      show (PreToken.node ITag.tor :: (preorder a ++ preorder b)).getLast?
        = some (PreToken.leaf g)
      rw [getLast?_cons_of_ne_nil _ (fun hc =>
          preorder_ne_nil b (List.append_eq_nil_iff.mp hc).2),
        getLast?_append_right_of_ne_nil _ (preorder_ne_nil b)]
      exact hg

/-- **A reachable node read always has a nonempty tail.**  If a state reachable from the driver
start for `c` is about to read a `node` token, the remaining tail is nonempty (a node is never the
last token of a preorder stream) — the node-branch shape fact of `DriverStepFits`. -/
theorem reachable_node_tail_ne_nil {n : Nat} (c : CircuitTree n) (j : Nat) (tag : ITag)
    (toks' : List (PreToken n))
    (h : (DriveState.step^[j] (⟨preorder c, [], [], [], false⟩ : DriveState n)).toks
      = PreToken.node tag :: toks') :
    toks' ≠ [] := by
  intro hnil
  subst hnil
  have hsuffix := toks_iterate_suffix (⟨preorder c, [], [], [], false⟩ : DriveState n) j
  rw [h] at hsuffix
  obtain ⟨pre, hpre⟩ := hsuffix
  obtain ⟨g, hg⟩ := preorder_getLast_leaf c
  rw [show (preorder c) = pre ++ [PreToken.node tag] from hpre.symm,
    getLast?_append_right_of_ne_nil pre (by simp)] at hg
  simp at hg

end ContractExpansion
end Frontier
end Pnp4
