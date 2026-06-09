import Pnp4.Frontier.ContractExpansion.TreeMCSPDriveStack

/-!
# `DriveState.step` — D2t-5b: the small-step (one-micro-step) driver semantics

`drive` (`TreeMCSPDriveStack`) is the **big-step** preorder-streaming driver: a `foldl` over the certificate
tokens whose `settle` arm runs an *unbounded* completion cascade per leaf.  The on-tape machine, however,
runs a single self-terminating loop (`loopUntilSink`, with one **measure**); each loop iteration performs
exactly **one** primitive action.  This module supplies the matching **small-step** semantics — the spec
the flat on-tape loop body realises micro-step for micro-step — and proves it equivalent to `drive` (hence
to `flatten`).

A micro-state `DriveState` carries the unread preorder tokens, the WORK list, the two stacks, and a
`settling` flag (we are inside a completion cascade, the top value being the just-completed subtree's root).
`DriveState.step` does **one** action:

* **settling, control stack empty** — the cascade is done; clear the flag (resume reading);
* **settling, top frame `rem = 1`** — the gate is complete: pop the frame, emit it over the value-stack
  operands, push the new index, stay settling (it settles into *its* parent);
* **settling, top frame `rem ≥ 2`** — decrement the frame, clear the flag (await the next child);
* **reading a leaf** — emit the record, push its index, enter settling;
* **reading a node** — push a `(tag, arity)` frame, keep reading.

Results:

* `step_iterate_settle` / `step_iterate_processToken` / `step_iterate_drive` — iterating `step` reproduces
  `settle` / `processToken` / `drive` (∃ a step count); the existential absorbs the variable per-token
  strides, exactly what `loopUntilSink_reachesSink` consumes.
* `driveStep_out_eq_flatten` — **the keystone**: run from `⟨preorder c, [], [], [], false⟩`, the small-step
  driver leaves `(flatten c).gates` (the postorder flatten) in WORK.
* `DriveState.mu` + `mu_step_lt` + `step_terminal` — a measure that **strictly decreases** off the terminal
  states (toks exhausted, not settling) and fixes them: the loop terminates.  This is the `μ` the on-tape
  `loopUntilSink_reachesSink` driver will use.

**Progress classification (AGENTS.md): Infrastructure** — a pure small-step driver spec proven against the
verified big-step `drive`/`flatten`; builds no machine and proves no separation.  Standard
`[propext, Classical.choice, Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-- A micro-state of the preorder-streaming driver: the unread preorder `toks`, the WORK list `out`, the
control stack `ctrl`, the value stack `val`, and a `settling` flag (inside a completion cascade — the top
of `val` is the just-completed subtree's root index). -/
structure DriveState (n : Nat) where
  toks : List (PreToken n)
  out : List (SLGate n)
  ctrl : List (ITag × Nat)
  val : List Nat
  settling : Bool

/-- One primitive driver action (the unit the on-tape `loopUntilSink` body performs per iteration). -/
def DriveState.step {n : Nat} : DriveState n → DriveState n
  | ⟨toks, out, ctrl, val, true⟩ =>
      match ctrl with
      | [] => ⟨toks, out, [], val, false⟩
      | (tag, rem) :: ctrl' =>
          if rem = 1 then
            match tag, val with
            | ITag.tnot, i :: vs =>
                ⟨toks, out ++ [SLGate.notGate i], ctrl', out.length :: vs, true⟩
            | ITag.tand, i2 :: i1 :: vs =>
                ⟨toks, out ++ [SLGate.andGate i1 i2], ctrl', out.length :: vs, true⟩
            | ITag.tor, i2 :: i1 :: vs =>
                ⟨toks, out ++ [SLGate.orGate i1 i2], ctrl', out.length :: vs, true⟩
            | _, _ => ⟨toks, out, (tag, rem) :: ctrl', val, false⟩
          else
            ⟨toks, out, (tag, rem - 1) :: ctrl', val, false⟩
  | ⟨toks, out, ctrl, val, false⟩ =>
      match toks with
      | [] => ⟨toks, out, ctrl, val, false⟩
      | PreToken.leaf g :: toks' => ⟨toks', out ++ [g], ctrl, out.length :: val, true⟩
      | PreToken.node tag :: toks' => ⟨toks', out, (tag, tag.arity) :: ctrl, val, false⟩

/-- Inject a `(WORK, control, value)` triple (the result type of `settle`/`processToken`/`drive`) back into
a non-settling `DriveState` with a given remaining-token list — the shape the iteration lemmas land in. -/
def DriveState.ofTriple {n : Nat} (toks : List (PreToken n))
    (r : List (SLGate n) × List (ITag × Nat) × List Nat) : DriveState n :=
  ⟨toks, r.1, r.2.1, r.2.2, false⟩

/-! ### Iterating `step` reproduces the big-step driver -/

/-- **Settle cascade.**  From a settling state, iterating `step` runs the whole `settle` cascade on the
control stack and clears the flag — landing in exactly `settle out ctrl val`.  Induction on the control
stack (matching `settle`'s structural recursion); each completed frame is one `step`, the final
decrement / empty-stack step clears `settling`. -/
theorem step_iterate_settle {n : Nat} (toks : List (PreToken n)) :
    ∀ (ctrl : List (ITag × Nat)) (out : List (SLGate n)) (val : List Nat),
      ∃ k, DriveState.step^[k] ⟨toks, out, ctrl, val, true⟩
        = DriveState.ofTriple toks (settle out ctrl val) := by
  intro ctrl
  induction ctrl with
  | nil =>
      intro out val
      exact ⟨1, by simp [DriveState.step, DriveState.ofTriple, settle]⟩
  | cons f ctrl' ih =>
      obtain ⟨tag, rem⟩ := f
      intro out val
      by_cases hrem : rem = 1
      · subst hrem
        cases tag with
        | tnot =>
            cases val with
            | nil => exact ⟨1, by simp [DriveState.step, DriveState.ofTriple, settle]⟩
            | cons i vs =>
                obtain ⟨k', hk'⟩ := ih (out ++ [SLGate.notGate i]) (out.length :: vs)
                refine ⟨k' + 1, ?_⟩
                have h1 : DriveState.step ⟨toks, out, (ITag.tnot, 1) :: ctrl', i :: vs, true⟩
                    = ⟨toks, out ++ [SLGate.notGate i], ctrl', out.length :: vs, true⟩ := by
                  simp [DriveState.step]
                have hs : settle out ((ITag.tnot, 1) :: ctrl') (i :: vs)
                    = settle (out ++ [SLGate.notGate i]) ctrl' (out.length :: vs) := by
                  simp [settle]
                rw [Function.iterate_succ_apply, h1, hk', hs]
        | tand =>
            cases val with
            | nil => exact ⟨1, by simp [DriveState.step, DriveState.ofTriple, settle]⟩
            | cons i2 rest =>
                cases rest with
                | nil => exact ⟨1, by simp [DriveState.step, DriveState.ofTriple, settle]⟩
                | cons i1 vs =>
                    obtain ⟨k', hk'⟩ := ih (out ++ [SLGate.andGate i1 i2]) (out.length :: vs)
                    refine ⟨k' + 1, ?_⟩
                    have h1 : DriveState.step ⟨toks, out, (ITag.tand, 1) :: ctrl', i2 :: i1 :: vs, true⟩
                        = ⟨toks, out ++ [SLGate.andGate i1 i2], ctrl', out.length :: vs, true⟩ := by
                      simp [DriveState.step]
                    have hs : settle out ((ITag.tand, 1) :: ctrl') (i2 :: i1 :: vs)
                        = settle (out ++ [SLGate.andGate i1 i2]) ctrl' (out.length :: vs) := by
                      simp [settle]
                    rw [Function.iterate_succ_apply, h1, hk', hs]
        | tor =>
            cases val with
            | nil => exact ⟨1, by simp [DriveState.step, DriveState.ofTriple, settle]⟩
            | cons i2 rest =>
                cases rest with
                | nil => exact ⟨1, by simp [DriveState.step, DriveState.ofTriple, settle]⟩
                | cons i1 vs =>
                    obtain ⟨k', hk'⟩ := ih (out ++ [SLGate.orGate i1 i2]) (out.length :: vs)
                    refine ⟨k' + 1, ?_⟩
                    have h1 : DriveState.step ⟨toks, out, (ITag.tor, 1) :: ctrl', i2 :: i1 :: vs, true⟩
                        = ⟨toks, out ++ [SLGate.orGate i1 i2], ctrl', out.length :: vs, true⟩ := by
                      simp [DriveState.step]
                    have hs : settle out ((ITag.tor, 1) :: ctrl') (i2 :: i1 :: vs)
                        = settle (out ++ [SLGate.orGate i1 i2]) ctrl' (out.length :: vs) := by
                      simp [settle]
                    rw [Function.iterate_succ_apply, h1, hk', hs]
      · refine ⟨1, ?_⟩
        simp [DriveState.step, DriveState.ofTriple, settle, hrem]

/-- **One token.**  From a reading state, iterating `step` consumes exactly one preorder token and
reproduces `processToken` — for a node, one push step; for a leaf, the push step then the settle cascade
(via `step_iterate_settle`). -/
theorem step_iterate_processToken {n : Nat} (out : List (SLGate n)) (ctrl : List (ITag × Nat))
    (val : List Nat) (tok : PreToken n) (toks : List (PreToken n)) :
    ∃ k, DriveState.step^[k] ⟨tok :: toks, out, ctrl, val, false⟩
      = DriveState.ofTriple toks (processToken (out, ctrl, val) tok) := by
  cases tok with
  | node tag =>
      refine ⟨1, ?_⟩
      simp [DriveState.step, DriveState.ofTriple, processToken]
  | leaf g =>
      obtain ⟨k', hk'⟩ := step_iterate_settle toks ctrl (out ++ [g]) (out.length :: val)
      refine ⟨k' + 1, ?_⟩
      have h1 : DriveState.step ⟨PreToken.leaf g :: toks, out, ctrl, val, false⟩
          = ⟨toks, out ++ [g], ctrl, out.length :: val, true⟩ := by
        simp [DriveState.step]
      rw [Function.iterate_succ_apply, h1, hk']
      simp [processToken]

/-- **Whole stream.**  From a reading state, iterating `step` runs `drive` to completion, ending with the
tokens exhausted (`ofTriple []`).  Induction on the token list, threading `step_iterate_processToken` and
the `foldl` step of `drive`. -/
theorem step_iterate_drive {n : Nat} :
    ∀ (toks : List (PreToken n)) (out : List (SLGate n)) (ctrl : List (ITag × Nat)) (val : List Nat),
      ∃ k, DriveState.step^[k] ⟨toks, out, ctrl, val, false⟩
        = DriveState.ofTriple [] (drive toks (out, ctrl, val)) := by
  intro toks
  induction toks with
  | nil =>
      intro out ctrl val
      exact ⟨0, by simp [DriveState.ofTriple, drive]⟩
  | cons tok toks' ih =>
      intro out ctrl val
      obtain ⟨k₁, hk₁⟩ := step_iterate_processToken out ctrl val tok toks'
      obtain ⟨k₂, hk₂⟩ := ih (processToken (out, ctrl, val) tok).1
        (processToken (out, ctrl, val) tok).2.1 (processToken (out, ctrl, val) tok).2.2
      refine ⟨k₂ + k₁, ?_⟩
      have hofeq : DriveState.ofTriple toks' (processToken (out, ctrl, val) tok)
          = ⟨toks', (processToken (out, ctrl, val) tok).1, (processToken (out, ctrl, val) tok).2.1,
              (processToken (out, ctrl, val) tok).2.2, false⟩ := rfl
      rw [Function.iterate_add_apply, hk₁, hofeq, hk₂]
      rfl

/-! ### The driver keystone -/

/-- `step` run from the empty initial state reproduces `drive (preorder c) ([], [], [])`. -/
theorem driveStep_drive {n : Nat} (c : CircuitTree n) :
    ∃ k, DriveState.step^[k] ⟨preorder c, [], [], [], false⟩
      = DriveState.ofTriple [] (drive (preorder c) ([], [], [])) :=
  step_iterate_drive (preorder c) [] [] []

/-- **D2t-5b small-step driver keystone.**  Run from `⟨preorder c, [], [], [], false⟩`, the small-step
driver leaves exactly `(flatten c).gates` — the postorder flatten — in WORK.  Bridges the on-tape
single-loop body (one `step` per iteration) to the verified `flatten`. -/
theorem driveStep_out_eq_flatten {n : Nat} (c : CircuitTree n) :
    ∃ k, (DriveState.step^[k] ⟨preorder c, [], [], [], false⟩).out = (CircuitTree.flatten c).gates := by
  obtain ⟨k, hk⟩ := driveStep_drive c
  refine ⟨k, ?_⟩
  rw [hk]
  show driveWORK c = (CircuitTree.flatten c).gates
  exact driveWORK_eq_flatten c

/-! ### Termination measure (the `μ` for the on-tape `loopUntilSink` driver) -/

/-- A state is **terminal** when the tokens are exhausted and we are not settling — the loop's halt
condition (the certificate has been fully transcoded). -/
def DriveState.terminal {n : Nat} (s : DriveState n) : Prop :=
  s.settling = false ∧ s.toks = []

/-- The driver **measure**: each unread token costs `3` (a read plus its at-most-two future settle touches),
each pending control frame costs its `remaining` count (the settle touches it still needs), and the
`settling` flag costs `1` (the pending cascade resumption).  Strictly decreases off terminal states. -/
def DriveState.mu {n : Nat} (s : DriveState n) : Nat :=
  3 * s.toks.length + (s.ctrl.map Prod.snd).sum + (if s.settling then 1 else 0)

/-- `step` fixes the terminal states (the loop idles once the certificate is consumed). -/
theorem DriveState.step_terminal {n : Nat} (s : DriveState n) (h : s.terminal) : s.step = s := by
  obtain ⟨hset, htoks⟩ := h
  obtain ⟨toks, out, ctrl, val, settling⟩ := s
  subst hset; subst htoks
  rfl

/-- **The measure strictly decreases** on every non-terminal state — so the on-tape `loopUntilSink` driver
terminates.  Case analysis on the action: settling steps drop a frame's count or the flag; a leaf read drops
`3` and adds the flag; a node read drops `3` and adds at most `2` (the arity) of future settle work. -/
theorem DriveState.mu_step_lt {n : Nat} (s : DriveState n) (h : ¬ s.terminal) : s.step.mu < s.mu := by
  obtain ⟨toks, out, ctrl, val, settling⟩ := s
  cases settling with
  | true =>
      cases ctrl with
      | nil => simp [DriveState.step, DriveState.mu]
      | cons f ctrl' =>
          obtain ⟨tag, rem⟩ := f
          by_cases hrem : rem = 1
          · subst hrem
            cases tag with
            | tnot =>
                cases val with
                | nil => simp [DriveState.step, DriveState.mu]
                | cons i vs => simp [DriveState.step, DriveState.mu]
            | tand =>
                cases val with
                | nil => simp [DriveState.step, DriveState.mu]
                | cons i2 rest =>
                    cases rest with
                    | nil => simp [DriveState.step, DriveState.mu]
                    | cons i1 vs => simp [DriveState.step, DriveState.mu]
            | tor =>
                cases val with
                | nil => simp [DriveState.step, DriveState.mu]
                | cons i2 rest =>
                    cases rest with
                    | nil => simp [DriveState.step, DriveState.mu]
                    | cons i1 vs => simp [DriveState.step, DriveState.mu]
          · simp [DriveState.step, DriveState.mu, hrem]
            omega
  | false =>
      cases toks with
      | nil => exact absurd ⟨rfl, rfl⟩ h
      | cons tok toks' =>
          cases tok with
          | leaf g =>
              simp [DriveState.step, DriveState.mu]
              omega
          | node tag =>
              cases tag <;> simp [DriveState.step, DriveState.mu, ITag.arity] <;> omega

end ContractExpansion
end Frontier
end Pnp4
