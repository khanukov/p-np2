/-
Copyright (c) 2026 Dmitry Khanukov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitry Khanukov
-/
module

public import Mathlib.Computability.TuringMachine.PostTuringMachine
import Mathlib.Data.Fintype.Basic

/-!
# Step counting and complexity classes P and NP for TM1

This file adds resource-bounded computation on top of the TM1 model from
`Mathlib.Computability.TuringMachine.PostTuringMachine`:

* `Turing.TM1.runN`: fuel-based execution — run a machine for (at most) `n`
  steps, staying put once the machine has halted.  This is related to the
  existing relational semantics by `Turing.TM1.mem_eval_iff_exists_runN`.
* `Turing.TM1.DecidesInTime`: a machine decides a language `L : Set (List Γ)`
  within a time bound `T`, where acceptance is expressed by a predicate
  `accept : Γ → Prop` applied to the tape symbol under the head in the halting
  configuration.
* `Turing.TM1.IsPolyTimeBound`: polynomial time bounds `T n ≤ n ^ k + k`.
* `Turing.TM1.InP`, `Turing.TM1.InNP`: the complexity classes P and NP over
  the alphabet `Γ` with acceptance predicate `accept`.
* `Turing.TM1.InP.subset_np`: **P ⊆ NP**.
* `Turing.TM1.InP.compl`: **P is closed under complement**, via the
  statement transformation `Turing.TM1.Stmt.mapHalt` that rewrites every
  `halt` instruction into "write the flipped verdict, then halt".  Because
  `write` costs zero steps in the TM1 cost model, the complement machine runs
  in *exactly* the same time bound.

## Design notes

* **Fuel-based `runN`.**  The existing semantics (`Turing.TM1.eval`, through
  `StateTransition.eval`) is relational and does not count steps.  `runN` is a
  total function, so time-bound statements are equalities about
  `runN M (T n) (init l)` rather than existentials over evaluation traces;
  monotonicity in the fuel (`runN_add`, `runN_of_halted`) replaces the usual
  reasoning about traces.  The bridge lemma `mem_eval_iff_exists_runN` shows
  the two semantics agree.
* **Acceptance predicate.**  TM1 has no accept/reject states; following the
  `eval` convention that the result of a computation is read off the final
  configuration, a computation *accepts* if the tape symbol under the head
  satisfies `accept` when the machine halts.  The classes are parameterized by
  `accept`, so any convention (a designated symbol, a Boolean flag, ...) is an
  instance.
* **Finite control.**  `Λ` (labels) and `σ` (internal state) are quantified
  with `Fintype` instances inside the class definitions.  This is
  load-bearing: with an infinite label or store type, a "machine" could smuggle
  unboundedly much information through a single transition, and the class
  would degenerate.  The alphabet `Γ` is likewise expected to be finite in
  applications, and the classes take `[Fintype Γ]`.
* **Certificates.**  `InNP` uses certificates `c : List Γ` appended to the
  input as `l ++ default :: c`.  For the containment P ⊆ NP the certificate
  bound is `0`, which forces `c = []`; since tapes are quotients by trailing
  blanks (`Turing.ListBlank`), `init (l ++ [default]) = init l` and the
  decider itself serves as the verifier.

## References

Requested in mathlib4 issue #35366; the complement construction follows the
textbook argument (swap the accepting and rejecting verdicts), adapted to the
TM1 cost model.
-/

@[expose] public section

open StateTransition

namespace Turing

namespace TM1

variable {Γ Λ σ : Type*}

/-! ### Halting and fuel-based execution -/

section Run

variable [Inhabited Γ]

theorem step_eq_none_iff {M : Λ → Stmt Γ Λ σ} {c : Cfg Γ Λ σ} :
    step M c = none ↔ c.l = none := by
  rcases c with ⟨_ | l, v, T⟩ <;> simp [step]

/-- Run a TM1 machine for (at most) `n` steps.  Once the machine halts
(`step` returns `none`), the configuration stays put, so `runN` is monotone
in the fuel in the sense of `runN_of_halted` and `runN_add`. -/
def runN (M : Λ → Stmt Γ Λ σ) : ℕ → Cfg Γ Λ σ → Cfg Γ Λ σ
  | 0, c => c
  | n + 1, c => (step M c).elim c (runN M n)

@[simp] theorem runN_zero (M : Λ → Stmt Γ Λ σ) (c : Cfg Γ Λ σ) : runN M 0 c = c := rfl

theorem runN_succ_of_step_none {M : Λ → Stmt Γ Λ σ} {c : Cfg Γ Λ σ}
    (h : step M c = none) (n : ℕ) : runN M (n + 1) c = c := by
  simp [runN, h]

theorem runN_succ_of_step_some {M : Λ → Stmt Γ Λ σ} {c c' : Cfg Γ Λ σ}
    (h : step M c = some c') (n : ℕ) : runN M (n + 1) c = runN M n c' := by
  simp [runN, h]

/-- A halted configuration is a fixed point of `runN`. -/
theorem runN_of_halted {M : Λ → Stmt Γ Λ σ} {c : Cfg Γ Λ σ} (h : c.l = none) :
    ∀ n, runN M n c = c
  | 0 => rfl
  | n + 1 => runN_succ_of_step_none (step_eq_none_iff.2 h) n

/-- Running for `m + n` steps is running for `m` steps, then `n` more. -/
theorem runN_add (M : Λ → Stmt Γ Λ σ) (m n : ℕ) (c : Cfg Γ Λ σ) :
    runN M (m + n) c = runN M n (runN M m c) := by
  induction m generalizing c with
  | zero => rw [Nat.zero_add]; rfl
  | succ m ih =>
      rcases h : step M c with - | c'
      · rw [runN_succ_of_step_none h, runN_of_halted (step_eq_none_iff.1 h),
          runN_of_halted (step_eq_none_iff.1 h)]
      · rw [Nat.succ_add, runN_succ_of_step_some h, runN_succ_of_step_some h, ih]

/-- The halting verdict is stable: if the machine has halted after `n` steps,
running it longer does not change the configuration. -/
theorem runN_le {M : Λ → Stmt Γ Λ σ} {c : Cfg Γ Λ σ} {m n : ℕ} (hmn : m ≤ n)
    (h : (runN M m c).l = none) : runN M n c = runN M m c := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [runN_add, runN_of_halted h]

/-! ### Bridge to the relational semantics -/

/-- `runN` only produces reachable configurations. -/
theorem reaches_runN (M : Λ → Stmt Γ Λ σ) (n : ℕ) (c : Cfg Γ Λ σ) :
    Reaches (step M) c (runN M n c) := by
  induction n generalizing c with
  | zero => exact Relation.ReflTransGen.refl
  | succ n ih =>
      rcases h : step M c with - | c'
      · rw [runN_succ_of_step_none h]
        exact Relation.ReflTransGen.refl
      · rw [runN_succ_of_step_some h]
        exact Relation.ReflTransGen.head (by rw [h]; rfl) (ih c')

/-- If the machine halts within `n` steps, the halting configuration computed
by `runN` is the result of the relational semantics `StateTransition.eval`. -/
theorem runN_mem_eval {M : Λ → Stmt Γ Λ σ} {c : Cfg Γ Λ σ} {n : ℕ}
    (h : (runN M n c).l = none) : runN M n c ∈ StateTransition.eval (step M) c :=
  mem_eval.2 ⟨reaches_runN M n c, step_eq_none_iff.2 h⟩

/-- Conversely, any result of the relational semantics is reached by `runN`
with some amount of fuel. -/
theorem exists_runN_of_mem_eval {M : Λ → Stmt Γ Λ σ} {c b : Cfg Γ Λ σ}
    (h : b ∈ StateTransition.eval (step M) c) : ∃ n, runN M n c = b := by
  obtain ⟨hr, hb⟩ := mem_eval.1 h
  clear h
  induction hr using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, rfl⟩
  | head hstep _ ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, by rw [runN_succ_of_step_some (Option.mem_def.1 hstep), hn]⟩

/-- The fuel-based and the relational semantics agree. -/
theorem mem_eval_iff_exists_runN {M : Λ → Stmt Γ Λ σ} {c b : Cfg Γ Λ σ} :
    b ∈ StateTransition.eval (step M) c ↔ (∃ n, runN M n c = b) ∧ b.l = none := by
  constructor
  · intro h
    obtain ⟨hr, hb⟩ := mem_eval.1 h
    exact ⟨exists_runN_of_mem_eval h, step_eq_none_iff.1 hb⟩
  · rintro ⟨⟨n, rfl⟩, hb⟩
    exact runN_mem_eval hb

end Run

/-! ### Time-bounded decision -/

section Decides

variable [Inhabited Γ] [Inhabited Λ] [Inhabited σ]

/-- `M` accepts the input `l` within `t` steps: after `t` steps starting from
`init l` the machine has halted, and the tape symbol under the head satisfies
`accept`. -/
def AcceptsIn (M : Λ → Stmt Γ Λ σ) (accept : Γ → Prop) (l : List Γ) (t : ℕ) : Prop :=
  (runN M t (init l)).l = none ∧ accept (runN M t (init l)).Tape.head

/-- `M` decides the language `L` within the time bound `T`: on every input
`l`, the machine halts within `T l.length` steps and the acceptance verdict
(read off the tape symbol under the head) matches membership in `L`. -/
def DecidesInTime (M : Λ → Stmt Γ Λ σ) (accept : Γ → Prop) (L : Set (List Γ))
    (T : ℕ → ℕ) : Prop :=
  ∀ l : List Γ, (runN M (T l.length) (init l)).l = none ∧
    (accept (runN M (T l.length) (init l)).Tape.head ↔ l ∈ L)

/-- Enlarging the time bound preserves the decision: the halting configuration
is stable under extra fuel. -/
theorem DecidesInTime.mono {M : Λ → Stmt Γ Λ σ} {accept : Γ → Prop}
    {L : Set (List Γ)} {T T' : ℕ → ℕ} (h : DecidesInTime M accept L T)
    (hT : ∀ n, T n ≤ T' n) : DecidesInTime M accept L T' := by
  intro l
  rw [runN_le (hT l.length) (h l).1]
  exact h l

end Decides

/-! ### Polynomial time bounds -/

/-- A time bound is polynomial if it is eventually dominated by `n ^ k + k`.
This lightweight formulation avoids importing polynomial algebra into the
computability hierarchy. -/
def IsPolyTimeBound (T : ℕ → ℕ) : Prop :=
  ∃ k : ℕ, ∀ n, T n ≤ n ^ k + k

theorem IsPolyTimeBound.const (m : ℕ) : IsPolyTimeBound fun _ => m :=
  ⟨m, fun n => Nat.le_add_left m (n ^ m)⟩

theorem IsPolyTimeBound.id : IsPolyTimeBound fun n => n :=
  ⟨1, fun n => by simp⟩

/-! ### The classes P and NP -/

section Classes

variable (Γ) in
/-- A polynomial-time decider for the language `L`: a TM1 machine with finite
control (`Fintype` labels and store) together with a polynomial time bound
within which it decides `L`. -/
structure PTimeDecider (accept : Γ → Prop) (L : Set (List Γ)) [Inhabited Γ] where
  /-- The label (function name) type of the machine. -/
  Λ : Type
  /-- The internal store type of the machine. -/
  σ : Type
  /-- The label type is finite. -/
  [fintypeΛ : Fintype Λ]
  /-- The store type is finite. -/
  [fintypeσ : Fintype σ]
  /-- The label type is inhabited (the default label is the entry point). -/
  [inhabitedΛ : Inhabited Λ]
  /-- The store type is inhabited (the default value is the initial store). -/
  [inhabitedσ : Inhabited σ]
  /-- The machine. -/
  M : Λ → Stmt Γ Λ σ
  /-- The time bound. -/
  T : ℕ → ℕ
  /-- The time bound is polynomial. -/
  poly : IsPolyTimeBound T
  /-- The machine decides `L` within the time bound. -/
  decides : DecidesInTime M accept L T

variable (Γ) in
/-- A polynomial-time verifier for the language `L`: membership `l ∈ L` holds
iff some certificate `c` of polynomially bounded length makes the verifier
accept the padded input `l ++ default :: c` in polynomial time (in the length
of `l`). -/
structure PTimeVerifier (accept : Γ → Prop) (L : Set (List Γ)) [Inhabited Γ] where
  /-- The label (function name) type of the verifier. -/
  Λ : Type
  /-- The internal store type of the verifier. -/
  σ : Type
  /-- The label type is finite. -/
  [fintypeΛ : Fintype Λ]
  /-- The store type is finite. -/
  [fintypeσ : Fintype σ]
  /-- The label type is inhabited. -/
  [inhabitedΛ : Inhabited Λ]
  /-- The store type is inhabited. -/
  [inhabitedσ : Inhabited σ]
  /-- The verifier machine. -/
  M : Λ → Stmt Γ Λ σ
  /-- The certificate length bound. -/
  p : ℕ → ℕ
  /-- The time bound. -/
  T : ℕ → ℕ
  /-- The certificate length bound is polynomial. -/
  polyCert : IsPolyTimeBound p
  /-- The time bound is polynomial. -/
  polyTime : IsPolyTimeBound T
  /-- Soundness and completeness of the verifier. -/
  verifies : ∀ l : List Γ, l ∈ L ↔ ∃ c : List Γ,
    c.length ≤ p l.length ∧ AcceptsIn M accept (l ++ default :: c) (T l.length)

attribute [instance] PTimeDecider.fintypeΛ PTimeDecider.fintypeσ
  PTimeDecider.inhabitedΛ PTimeDecider.inhabitedσ
attribute [instance] PTimeVerifier.fintypeΛ PTimeVerifier.fintypeσ
  PTimeVerifier.inhabitedΛ PTimeVerifier.inhabitedσ

variable (Γ) in
/-- The class **P** over the alphabet `Γ` with acceptance predicate `accept`:
languages decided by a TM1 machine with finite control in polynomial time. -/
def InP [Inhabited Γ] [Fintype Γ] (accept : Γ → Prop) (L : Set (List Γ)) : Prop :=
  Nonempty (PTimeDecider Γ accept L)

variable (Γ) in
/-- The class **NP** over the alphabet `Γ` with acceptance predicate `accept`:
languages with a polynomial-time verifier accepting polynomially long
certificates. -/
def InNP [Inhabited Γ] [Fintype Γ] (accept : Γ → Prop) (L : Set (List Γ)) : Prop :=
  Nonempty (PTimeVerifier Γ accept L)

/-- `InP` is inhabited: the machine that halts immediately decides — in one
step — the language of lists whose head symbol (`default` for the empty list)
satisfies `accept`. -/
theorem inP_head [Inhabited Γ] [Fintype Γ] (accept : Γ → Prop) :
    InP Γ accept {l : List Γ | accept l.headI} := by
  refine ⟨{ Λ := Unit, σ := Unit, M := fun _ => .halt, T := fun _ => 1,
            poly := .const 1, decides := fun l => ⟨rfl, ?_⟩ }⟩
  change accept (Tape.mk₁ l).head ↔ accept l.headI
  simp [Tape.mk₁, Tape.mk₂]

end Classes

/-! ### P ⊆ NP -/

section PSubNP

variable [Inhabited Γ]

/-- Appending one blank to the input does not change the initial
configuration, because tapes are quotients by trailing blanks. -/
theorem init_append_default [Inhabited Λ] [Inhabited σ] (l : List Γ) :
    (init (l ++ [(default : Γ)]) : Cfg Γ Λ σ) = init l := by
  change Cfg.mk _ _ (Tape.mk₁ (l ++ [(default : Γ)])) = Cfg.mk _ _ (Tape.mk₁ l)
  congr 1
  change Tape.mk' (ListBlank.mk []) (ListBlank.mk (l ++ [default]))
      = Tape.mk' (ListBlank.mk []) (ListBlank.mk l)
  congr 1
  exact Quotient.sound' (Or.inr ⟨1, rfl⟩)

/-- A polynomial-time decider is a polynomial-time verifier for certificates
of length `0`. -/
def PTimeDecider.toVerifier {accept : Γ → Prop} {L : Set (List Γ)}
    (D : PTimeDecider Γ accept L) : PTimeVerifier Γ accept L where
  Λ := D.Λ
  σ := D.σ
  M := D.M
  p := fun _ => 0
  T := D.T
  polyCert := .const 0
  polyTime := D.poly
  verifies := by
    intro l
    constructor
    · intro hl
      refine ⟨[], Nat.le_refl 0, ?_⟩
      unfold AcceptsIn
      rw [show l ++ (default : Γ) :: [] = l ++ [default] from rfl, init_append_default]
      exact ⟨(D.decides l).1, (D.decides l).2.2 hl⟩
    · rintro ⟨c, hc, hacc⟩
      obtain rfl : c = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hc)
      unfold AcceptsIn at hacc
      rw [show l ++ (default : Γ) :: [] = l ++ [default] from rfl,
        init_append_default] at hacc
      exact (D.decides l).2.1 hacc.2

/-- **P is contained in NP**: a decider is a verifier that ignores its
(empty) certificate. -/
theorem InP.subset_np [Fintype Γ] {accept : Γ → Prop} {L : Set (List Γ)}
    (h : InP Γ accept L) : InNP Γ accept L :=
  h.elim fun D => ⟨D.toVerifier⟩

end PSubNP

/-! ### P is closed under complement

The textbook argument "swap the accepting and rejecting states" takes the
following form in TM1, where acceptance is a predicate on the tape symbol
under the head: rewrite every `halt` instruction of the machine into
`write flip halt`, where `flip` maps accepted symbols to a fixed rejected
symbol and vice versa.  Since `write` costs zero steps in the TM1 cost model
(only `goto` and `halt` consume a step), the complement machine halts at
exactly the same step as the original, with the flipped verdict under the
head.
-/

section Complement

/-- Replace every `halt` leaf of a statement by `write f halt`. -/
def Stmt.mapHalt (f : Γ → σ → Γ) : Stmt Γ Λ σ → Stmt Γ Λ σ
  | .move d q => .move d (q.mapHalt f)
  | .write g q => .write g (q.mapHalt f)
  | .load g q => .load g (q.mapHalt f)
  | .branch g q₁ q₂ => .branch g (q₁.mapHalt f) (q₂.mapHalt f)
  | .goto g => .goto g
  | .halt => .write f .halt

variable [Inhabited Γ]

/-- Apply the halting rewrite to a configuration: if the configuration is
halted, write `f head var` under the head; otherwise leave it unchanged. -/
def writeHaltCfg (f : Γ → σ → Γ) (c : Cfg Γ Λ σ) : Cfg Γ Λ σ :=
  if c.l.isSome then c
  else ⟨none, c.var, c.Tape.write (f c.Tape.head c.var)⟩

theorem writeHaltCfg_of_isSome {f : Γ → σ → Γ} {c : Cfg Γ Λ σ}
    (h : c.l.isSome) : writeHaltCfg f c = c := if_pos h

@[simp] theorem writeHaltCfg_l {f : Γ → σ → Γ} (c : Cfg Γ Λ σ) :
    (writeHaltCfg f c).l = c.l := by
  unfold writeHaltCfg
  rcases h : c.l with - | l <;> simp [h]

/-- The single-step semantics of a `mapHalt`-rewritten statement: it produces
the same configuration, post-processed by `writeHaltCfg`. -/
theorem stepAux_mapHalt (f : Γ → σ → Γ) (q : Stmt Γ Λ σ) (v : σ) (T : Tape Γ) :
    stepAux (q.mapHalt f) v T = writeHaltCfg f (stepAux q v T) := by
  induction q generalizing v T with
  | move d q ih => exact ih _ _
  | write g q ih => exact ih _ _
  | load g q ih => exact ih _ _
  | branch g q₁ q₂ ih₁ ih₂ =>
      change stepAux (.branch g (q₁.mapHalt f) (q₂.mapHalt f)) v T = _
      unfold stepAux
      cases hg : g T.1 v
      · exact ih₂ _ _
      · exact ih₁ _ _
  | goto g =>
      exact (writeHaltCfg_of_isSome rfl).symm
  | halt =>
      change (⟨none, v, T.write (f T.1 v)⟩ : Cfg Γ Λ σ) = writeHaltCfg f ⟨none, v, T⟩
      simp [writeHaltCfg]

/-- The step function of the `mapHalt`-rewritten machine. -/
theorem step_mapHalt (f : Γ → σ → Γ) (M : Λ → Stmt Γ Λ σ) (c : Cfg Γ Λ σ) :
    step (fun l => (M l).mapHalt f) c = (step M c).map (writeHaltCfg f) := by
  rcases c with ⟨_ | l, v, T⟩
  · rfl
  · change some (stepAux ((M l).mapHalt f) v T) = some (writeHaltCfg f (stepAux (M l) v T))
    rw [stepAux_mapHalt]

/-- Runs of the `mapHalt`-rewritten machine are runs of the original machine,
post-processed by `writeHaltCfg` (for runs starting in a non-halted
configuration). -/
theorem runN_mapHalt (f : Γ → σ → Γ) (M : Λ → Stmt Γ Λ σ) (n : ℕ)
    (c : Cfg Γ Λ σ) (hc : c.l.isSome) :
    runN (fun l => (M l).mapHalt f) n c = writeHaltCfg f (runN M n c) := by
  induction n generalizing c with
  | zero => exact (writeHaltCfg_of_isSome hc).symm
  | succ n ih =>
      rcases hstep : step M c with - | d
      · rw [step_eq_none_iff] at hstep
        rw [hstep] at hc
        exact absurd hc (by simp)
      · have hstep' : step (fun l => (M l).mapHalt f) c = some (writeHaltCfg f d) := by
          rw [step_mapHalt, hstep, Option.map_some]
        rw [runN_succ_of_step_some hstep', runN_succ_of_step_some hstep]
        rcases hd : d.l with - | l
        · rw [runN_of_halted hd, runN_of_halted (by simp [hd])]
        · rw [writeHaltCfg_of_isSome (by simp [hd])]
          exact ih d (by simp [hd])

variable [Inhabited Λ] [Inhabited σ]

/-- If `M` decides `L`, then the `mapHalt`-rewritten machine (with the verdict
flip) decides the complement `Lᶜ` — within the **same** time bound. -/
theorem DecidesInTime.compl {M : Λ → Stmt Γ Λ σ} {accept : Γ → Prop}
    [DecidablePred accept] {L : Set (List Γ)} {T : ℕ → ℕ}
    (h : DecidesInTime M accept L T) {a₀ r₀ : Γ} (ha : accept a₀) (hr : ¬accept r₀) :
    DecidesInTime (fun l => (M l).mapHalt fun a _ => if accept a then r₀ else a₀)
      accept Lᶜ T := by
  intro l
  have hrun := runN_mapHalt (fun a _ => if accept a then r₀ else a₀) M
    (T l.length) (init l) (by simp [init])
  obtain ⟨hhalt, hacc⟩ := h l
  rw [hrun]
  unfold writeHaltCfg
  rw [hhalt]
  refine ⟨rfl, ?_⟩
  change accept ((_ : Tape Γ).write _).head ↔ _
  change accept (if accept (runN M (T l.length) (init l)).Tape.head then r₀ else a₀) ↔ _
  by_cases hh : accept (runN M (T l.length) (init l)).Tape.head
  · simp only [if_pos hh]
    exact iff_of_false hr fun hL => hL (hacc.1 hh)
  · simp only [if_neg hh]
    exact iff_of_true ha fun hL => hh (hacc.2 hL)

/-- The complement decider, packaged. -/
def PTimeDecider.compl {accept : Γ → Prop} [DecidablePred accept]
    {L : Set (List Γ)} (D : PTimeDecider Γ accept L) {a₀ r₀ : Γ}
    (ha : accept a₀) (hr : ¬accept r₀) : PTimeDecider Γ accept Lᶜ where
  Λ := D.Λ
  σ := D.σ
  M := fun l => (D.M l).mapHalt fun a _ => if accept a then r₀ else a₀
  T := D.T
  poly := D.poly
  decides := D.decides.compl ha hr

/-- **P is closed under complement.**  The acceptance predicate must be
decidable and non-degenerate (some symbol is accepting, some symbol is not);
the complement machine has the same label and store types and the same time
bound as the original. -/
theorem InP.compl [Fintype Γ] {accept : Γ → Prop}
    {L : Set (List Γ)} (h : InP Γ accept L) (ha : ∃ a, accept a)
    (hr : ∃ r, ¬accept r) : InP Γ accept Lᶜ := by
  classical
  obtain ⟨a₀, ha₀⟩ := ha
  obtain ⟨r₀, hr₀⟩ := hr
  exact h.elim fun D => ⟨D.compl ha₀ hr₀⟩

/-- **P = coP**, stated as an equivalence. -/
theorem inP_compl_iff [Fintype Γ] {accept : Γ → Prop}
    {L : Set (List Γ)} (ha : ∃ a, accept a) (hr : ∃ r, ¬accept r) :
    InP Γ accept Lᶜ ↔ InP Γ accept L := by
  constructor
  · intro h
    simpa using h.compl ha hr
  · intro h
    exact h.compl ha hr

end Complement

end TM1

end Turing
