/-
Copyright (c) 2026 Dmitry Khanukov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitry Khanukov
-/

module

public import Cslib.Computability.Machines.Turing.SingleTape.Deterministic

/-!
# Tape relabeling for single-tape Turing machines

> **DRAFT — not yet compiled.** This file is part of the PR-3 toolkit draft for the
> complexity-class development. Every referenced library identifier has been checked against
> the CSLib/Mathlib sources, but the proofs have not been elaborated by Lean.

This file defines maps of tapes along a function on the alphabet
(`StackTape.map`, `BiTape.map`) and the machine transformer
`SingleTapeTM.relabelComputer`, which runs a machine over an alphabet `A` on a tape over a
larger alphabet `B`, along an injection `f : A → B` with retraction `g : B → Option A`.
On a head symbol outside the range of `f` (that is, `g` returns `none`), the relabeled
machine halts in place after one step.

## Main definitions

* `StackTape.map`, `BiTape.map`: map a function over the entries of a tape. Blanks are
  preserved, so the no-trailing-blank invariant of `StackTape` is maintained and
  `BiTape.map_mk₁` holds on the nose — no quotients, no normalization step.
* `SingleTapeTM.relabelComputer f g tm`: `tm` simulated over the larger alphabet.

## Main results

* `SingleTapeTM.relabelComputer_outputsWithinTime`: the simulation is step-for-step —
  a run of `tm` of length at most `t` transports to a run of the relabeled machine of
  length at most `t`, with input and output mapped along `f`. The proof is an instance of
  `Relation.RelatesWithinSteps.map`: the configuration map `⟨q, tape⟩ ↦ ⟨q, tape.map f⟩`
  is a homomorphism of transition relations. No new step-counting semantics is introduced.
* `SingleTapeTM.relabelComputer_outputsWithinTime_of_lower_eq_none`: on an input whose
  first symbol is outside the range of `f`, the relabeled machine halts in place in one
  step, leaving the tape unchanged.

## Placement

The `StackTape.map`/`BiTape.map` sections are natural candidates for upstreaming into
`Cslib.Foundations.Data.StackTape` and `Cslib.Foundations.Data.BiTape`; they are kept here
in the draft so that the PR is self-contained. Final placement is a maintainer call to be
settled on Zulip together with the namespace layout of the `Complexity/` directory.
-/

@[expose] public section

open Relation

namespace Cslib.Turing

open _root_.Turing

namespace StackTape

variable {A B : Type*}

/-- Map a function over the entries of a `StackTape`. Entries `some a` become
`some (f a)` and blanks stay blank, so the no-trailing-blank invariant is preserved. -/
def map (f : A → B) (s : StackTape A) : StackTape B :=
  ⟨s.toList.map (Option.map f), by
    intro h
    rw [List.getLast?_map] at h
    obtain ⟨o, ho, hnone⟩ := Option.map_eq_some_iff.mp h
    rw [Option.map_eq_none_iff] at hnone
    exact s.toList_getLast?_ne_some_none (hnone ▸ ho)⟩

@[simp]
theorem toList_map (f : A → B) (s : StackTape A) :
    (s.map f).toList = s.toList.map (Option.map f) := rfl

@[simp]
theorem map_nil (f : A → B) : (nil : StackTape A).map f = nil := rfl

@[simp]
theorem head_map (f : A → B) (s : StackTape A) : (s.map f).head = s.head.map f := by
  obtain ⟨l, hl⟩ := s
  cases l <;> rfl

@[simp]
theorem tail_map (f : A → B) (s : StackTape A) : (s.map f).tail = s.tail.map f := by
  obtain ⟨l, hl⟩ := s
  cases l <;> rfl

@[simp]
theorem map_cons (f : A → B) (o : Option A) (s : StackTape A) :
    (cons o s).map f = cons (o.map f) (s.map f) := by
  rw [eq_iff]
  constructor
  · rw [head_map, head_cons, head_cons]
  · rw [tail_map, tail_cons, tail_cons]

@[simp]
theorem map_mapSome (f : A → B) (l : List A) : (mapSome l).map f = mapSome (l.map f) := by
  apply toList_injective
  simp [mapSome, List.map_map, Function.comp_def]

end StackTape

namespace BiTape

variable {A B : Type*}

/-- Map a function over the entries of a `BiTape`, cellwise. Blanks stay blank. -/
def map (f : A → B) (t : BiTape A) : BiTape B :=
  ⟨t.head.map f, t.left.map f, t.right.map f⟩

@[simp]
theorem head_map (f : A → B) (t : BiTape A) : (t.map f).head = t.head.map f := rfl

@[simp]
theorem left_map (f : A → B) (t : BiTape A) : (t.map f).left = t.left.map f := rfl

@[simp]
theorem right_map (f : A → B) (t : BiTape A) : (t.map f).right = t.right.map f := rfl

@[simp]
theorem map_nil (f : A → B) : (nil : BiTape A).map f = nil := rfl

/-- Rendering a word and then relabeling the tape is relabeling the word and rendering it:
the map of tapes restricts to the map of words, with no normalization step in between. -/
@[simp]
theorem map_mk₁ (f : A → B) (l : List A) : (mk₁ l).map f = mk₁ (l.map f) := by
  cases l with
  | nil => rfl
  | cons a t => simp [mk₁, map]

@[simp]
theorem map_write (f : A → B) (t : BiTape A) (a : Option A) :
    (t.write a).map f = (t.map f).write (a.map f) := rfl

@[simp]
theorem map_moveLeft (f : A → B) (t : BiTape A) : t.moveLeft.map f = (t.map f).moveLeft := by
  simp [map, moveLeft]

@[simp]
theorem map_moveRight (f : A → B) (t : BiTape A) :
    t.moveRight.map f = (t.map f).moveRight := by
  simp [map, moveRight]

theorem map_move (f : A → B) (t : BiTape A) (d : Dir) :
    (t.move d).map f = (t.map f).move d := by
  cases d <;> simp [move]

theorem map_optionMove (f : A → B) (t : BiTape A) (d : Option Dir) :
    (t.optionMove d).map f = (t.map f).optionMove d := by
  cases d <;> simp [optionMove, map_move]

end BiTape

namespace SingleTapeTM

variable {A B : Type} [Inhabited A] [Fintype A] [Inhabited B] [Fintype B]

/--
Run a Turing machine `tm` over the alphabet `A` on a tape over a larger alphabet `B`,
along `f : A → B` with retraction `g : B → Option A`.

The relabeled machine has the same states as `tm`. On a blank it behaves as `tm` on a
blank; on a head symbol `b` with `g b = some a` it behaves as `tm` on `a`, writing symbols
through `f`; on a head symbol outside the range of `f` (`g b = none`) it rewrites the
symbol unchanged and halts in place. The simulation is step-for-step
(`relabelComputer_outputsWithinTime`): no time is lost or gained, so time bounds transfer
verbatim.
-/
def relabelComputer (f : A → B) (g : B → Option A) (tm : SingleTapeTM A) :
    SingleTapeTM B where
  State := tm.State
  q₀ := tm.q₀
  tr q s :=
    match s with
    | none =>
      match tm.tr q none with
      | ⟨⟨wr, dir⟩, q'⟩ => ⟨⟨wr.map f, dir⟩, q'⟩
    | some b =>
      match g b with
      | some a =>
        match tm.tr q (some a) with
        | ⟨⟨wr, dir⟩, q'⟩ => ⟨⟨wr.map f, dir⟩, q'⟩
      | none => ⟨⟨some b, none⟩, none⟩

/-- The configuration map of the relabeling simulation: keep the state, map the tape. -/
def toRelabelCfg (f : A → B) (g : B → Option A) (tm : SingleTapeTM A) (c : tm.Cfg) :
    (relabelComputer f g tm).Cfg :=
  ⟨c.state, c.BiTape.map f⟩

/--
`toRelabelCfg` is a homomorphism of transition relations: every step of `tm` is matched by
exactly one step of the relabeled machine. This is the single lemma from which the
simulation follows, via the existing `Relation.RelatesWithinSteps.map`.
-/
theorem relabelComputer_transitionRelation {f : A → B} {g : B → Option A}
    (hgf : ∀ a, g (f a) = some a) {tm : SingleTapeTM A} {c c' : tm.Cfg}
    (h : tm.TransitionRelation c c') :
    (relabelComputer f g tm).TransitionRelation
      (toRelabelCfg f g tm c) (toRelabelCfg f g tm c') := by
  obtain ⟨q, t⟩ := c
  cases q with
  | none => simp [TransitionRelation, step] at h
  | some q =>
    have h' : tm.step ⟨some q, t⟩ = some c' := h
    simp only [step] at h'
    generalize hM : tm.tr q t.head = result at h'
    obtain ⟨⟨wr, dir⟩, q''⟩ := result
    obtain rfl := Option.some.inj h'
    show (relabelComputer f g tm).step ⟨some q, t.map f⟩
        = some ⟨q'', ((t.write wr).optionMove dir).map f⟩
    cases ht : t.head with
    | none =>
      rw [ht] at hM
      simp only [step, BiTape.head_map, ht, Option.map_none, relabelComputer, hM,
        BiTape.map_optionMove, BiTape.map_write]
    | some a =>
      rw [ht] at hM
      simp only [step, BiTape.head_map, ht, Option.map_some, relabelComputer, hgf a, hM,
        BiTape.map_optionMove, BiTape.map_write]

theorem toRelabelCfg_initCfg (f : A → B) (g : B → Option A) (tm : SingleTapeTM A)
    (l : List A) :
    toRelabelCfg f g tm (tm.initCfg l) = (relabelComputer f g tm).initCfg (l.map f) := by
  simp [toRelabelCfg, initCfg, relabelComputer]

theorem toRelabelCfg_haltCfg (f : A → B) (g : B → Option A) (tm : SingleTapeTM A)
    (l : List A) :
    toRelabelCfg f g tm (tm.haltCfg l) = (relabelComputer f g tm).haltCfg (l.map f) := by
  simp [toRelabelCfg, haltCfg]

/--
Step-for-step simulation: a time-bounded run of `tm` transports along `f` to a
time-bounded run of the relabeled machine, with the *same* step bound.
Time is counted by the existing `OutputsWithinTime` on both sides.
-/
theorem relabelComputer_outputsWithinTime {f : A → B} {g : B → Option A}
    (hgf : ∀ a, g (f a) = some a) {tm : SingleTapeTM A} {l l' : List A} {t : ℕ}
    (h : tm.OutputsWithinTime l l' t) :
    (relabelComputer f g tm).OutputsWithinTime (l.map f) (l'.map f) t := by
  simp only [OutputsWithinTime] at h ⊢
  have hmap := RelatesWithinSteps.map (toRelabelCfg f g tm)
    (fun _ _ hcc' => relabelComputer_transitionRelation hgf hcc') h
  rw [toRelabelCfg_initCfg, toRelabelCfg_haltCfg] at hmap
  exact hmap

/--
On an input word whose first symbol is outside the range of `f`, the relabeled machine
halts in place in one step with the tape unchanged. This is the error path used by the
`P ⊆ NP` verifier: the well-formedness checker's error marker is out of range, so the
simulated decider never runs on an ill-formed input.
-/
theorem relabelComputer_outputsWithinTime_of_lower_eq_none {f : A → B} {g : B → Option A}
    {tm : SingleTapeTM A} {m : B} (hm : g m = none) (rest : List B) :
    (relabelComputer f g tm).OutputsWithinTime (m :: rest) (m :: rest) 1 := by
  refine RelatesWithinSteps.single ?_
  show (relabelComputer f g tm).step ((relabelComputer f g tm).initCfg (m :: rest))
      = some ((relabelComputer f g tm).haltCfg (m :: rest))
  simp only [step, initCfg, haltCfg, BiTape.mk₁, relabelComputer, hm, BiTape.write,
    BiTape.optionMove]

end SingleTapeTM

end Cslib.Turing
