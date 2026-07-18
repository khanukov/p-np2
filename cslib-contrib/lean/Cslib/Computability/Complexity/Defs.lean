/-
Copyright (c) 2026 Dmitry Khanukov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitry Khanukov
-/

module

public import Cslib.Computability.Machines.Turing.SingleTape.Deterministic
public import Mathlib.Computability.Language
public import Mathlib.Data.Fintype.OfMap
public import Mathlib.Data.Fintype.Sum

/-!
# Deciders and the complexity classes P and coP

This file defines what it means for a deterministic single-tape Turing machine
(`Cslib.Turing.SingleTapeTM`) to *decide* a language within a time bound,
and uses it to define the complexity class **P** of polynomial-time decidable languages
and the class **coP** of their complements, together with the closure theorem `coP = P`.

## Main definitions

* `DecSym Symbol`: the tape alphabet of a decider — the input symbols together with two
  dedicated verdict symbols `DecSym.verdict true` and `DecSym.verdict false`, distinct by
  construction from every input symbol and from the tape blank.
* `inputWord x`: the input word `x` as written on a decider's tape.
* `Cslib.Turing.SingleTapeTM.DecidesWithinTime tm L T`: on *every* input `x`, `tm` halts
  within `T x.length` steps with the tape holding exactly the verdict for `x ∈ L`.
* `P Symbol`: the languages over `Symbol` decidable in polynomial time
  (Sipser, *Introduction to the Theory of Computation*, 3rd ed., Definition 7.12;
  Arora–Barak, *Computational Complexity: A Modern Approach*, Definition 1.13).
* `coP Symbol`: the languages whose complement is in `P Symbol`.
* `Cslib.Turing.SingleTapeTM.mapHeadComputer`, `constComputer`: small concrete machines used
  as witnesses (a one-step head rewriter, and an erase-then-write-verdict machine).

## Main results

* `DecidesWithinTime.language_eq`: a machine decides at most one language — the verdict
  convention is canonical, not a parameter.
* `DecidesWithinTime.compl`: post-composing a decider with the verdict-flipping machine
  decides the complement, with one extra step.
* `coP_eq_P`, `P_eq_coP`, `compl_mem_P_iff`: `P` is closed under complement.
* `bot_mem_P`, `top_mem_P`: `P` is inhabited (`⊥` and `⊤` are decided by `constComputer`).
* `mem_P_of_polyTimeComputable`: a language whose characteristic word function is
  `SingleTapeTM.PolyTimeComputable` is in `P`.
* `mem_P_iff_timeBound`: `P` membership is equivalent to the
  `TimeComputable`/`PolyTimeComputable`-shaped packaging (a time bound `T : ℕ → ℕ`
  dominated by a `Polynomial ℕ`).

## Design notes

**Verdict convention (canonicity).** The deterministic model computes functions
`List Symbol → List Symbol` and, by an explicit design choice recorded in its module
docstring, does *not* make the halting state a member of the state type. Acceptance is
therefore expressed on the output tape: `tm` accepts (rejects) `x` iff it halts with tape
contents exactly `[DecSym.verdict true]` (`[DecSym.verdict false]`). This is precisely
Arora–Barak's Definition 1.13 — a language is in `P` iff a machine *computes its
characteristic function* in polynomial time — with the verdict symbols playing the role of
the output bits, and it is the tape-alphabet analogue of Sipser's dedicated
`q_accept`/`q_reject` states. There is no acceptance-convention *parameter* anywhere in
these definitions, so no invariance theorem is owed; instead, coherence is a theorem:
`DecidesWithinTime.language_eq` shows a machine decides at most one language (from
`SingleTapeTM.outputs_unique` and injectivity of `DecSym.verdict`). A Sipser-style
accept/reject-states presentation, mirroring `SingleTapeNTM.accept`/`accept_halting` on the
nondeterministic side, was considered and deliberately deferred: it would require changing
or wrapping the deterministic machine type, and can be added later with an equivalence
theorem.

**Input injectivity.** Distinct inputs reach the machine as distinct configurations; no
information is lost at the boundary. The chain is: `BiTape.mk₁_injective` (words render
faithfully onto the tape), `SingleTapeTM.initCfg_injective` (distinct words, distinct
initial configurations), `inputWord_injective` (tagging with `DecSym.input` is faithful),
and their composition `initCfg_inputWord_injective`. The verdict symbols cannot be spoofed:
`DecSym.input a`, `DecSym.verdict b`, and the blank (`none` at the tape level) are pairwise
non-confusable by construction.

**Totality.** `DecidesWithinTime` demands, on *every* input, halting within the stated
bound with an explicit two-sided verdict. Nothing is required of a machine only on
accepted inputs; there is no "accepts within time" one-sided notion in this file.

**Reuse.** Time is counted by the existing `SingleTapeTM.OutputsWithinTime` — the same
predicate used by `SingleTapeTM.TimeComputable` — and machine composition is the existing
`SingleTapeTM.compComputer` via `compComputer_outputsWithinTime`. Polynomial bounds are
`Polynomial ℕ` evaluated at the input length, exactly as in
`SingleTapeTM.PolyTimeComputable`; `mem_P_iff_timeBound` and `mem_P_of_polyTimeComputable`
make the correspondence explicit.

**Relation to `Acceptor`.** The automata-theoretic `Acceptor` typeclass assigns a language
to a *machine*. A bare `SingleTapeTM (DecSym Symbol)` decides a language only together with
a proof of `DecidesWithinTime` (machines that decide no language exist), so no `Acceptor`
instance is given here; `DecidesWithinTime.language_eq` shows the decided language is
unique whenever it exists. A bundled decider structure carrying an `Acceptor` instance can
be added later without changing the definitions in this file.

The classes are parametric in the (finite) input alphabet: `P Symbol : Set (Language
Symbol)`, matching the `Language`-valued conventions of the automata development.

## Future work

Verifier-based `NP` (with certificates ranging over bitstrings `List Bool` and pairs
encoded over `Symbol ⊕ Bool`), `P ⊆ NP`, a `DTIME` hierarchy with
`P = ⋃ p, DTIME (p.eval ·)`, and the equivalence with nondeterministic-machine acceptance.
None of these are claimed here.

## References

* M. Sipser, *Introduction to the Theory of Computation*, 3rd ed., Definitions 7.1, 7.12.
* S. Arora and B. Barak, *Computational Complexity: A Modern Approach*,
  Definitions 1.13, 2.1.
-/

@[expose] public section

open Relation

namespace Cslib

namespace Computability.Complexity

variable {Symbol : Type}

/--
The tape alphabet of a decider for languages over `Symbol`:
the input symbols together with two dedicated verdict symbols.
By construction, a verdict symbol is distinct from every input symbol,
and both are distinct from the tape blank
(which is `none : Option (DecSym Symbol)` at the tape level).
-/
inductive DecSym (Symbol : Type) : Type where
  /-- An input symbol. -/
  | input : Symbol → DecSym Symbol
  /-- A verdict symbol: `verdict true` for acceptance, `verdict false` for rejection. -/
  | verdict : Bool → DecSym Symbol
deriving DecidableEq

namespace DecSym

instance : Inhabited (DecSym Symbol) := ⟨verdict false⟩

/-- `DecSym Symbol` is the disjoint sum of the input symbols and the two verdict symbols. -/
def equivSum (Symbol : Type) : DecSym Symbol ≃ Symbol ⊕ Bool where
  toFun s :=
    match s with
    | input a => .inl a
    | verdict b => .inr b
  invFun s := s.elim input verdict
  left_inv s := by cases s <;> rfl
  right_inv s := by cases s <;> rfl

instance [Fintype Symbol] : Fintype (DecSym Symbol) :=
  Fintype.ofEquiv (Symbol ⊕ Bool) (equivSum Symbol).symm

/-- Tagging input symbols is injective. -/
theorem input_injective : Function.Injective (input (Symbol := Symbol)) := fun _ _ h => by
  simpa using h

/-- The two verdict symbols are distinct. -/
theorem verdict_injective : Function.Injective (verdict (Symbol := Symbol)) := fun _ _ h => by
  simpa using h

/-- Flip the verdict symbols, fixing every input symbol. -/
def flip : DecSym Symbol → DecSym Symbol
  | input a => input a
  | verdict b => verdict !b

end DecSym

/-- An input word as written on a decider's tape: every symbol is tagged `DecSym.input`. -/
def inputWord (x : List Symbol) : List (DecSym Symbol) := x.map .input

@[simp]
theorem length_inputWord (x : List Symbol) : (inputWord x).length = x.length := by
  simp [inputWord]

/-- Writing input words on the tape loses no information. -/
theorem inputWord_injective : Function.Injective (inputWord (Symbol := Symbol)) :=
  fun _ _ h => DecSym.input_injective.list_map h

end Computability.Complexity

namespace Turing.SingleTapeTM

open Cslib.Computability.Complexity

section MapHead

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

/--
The one-step machine that applies `f` to the symbol under the head and halts.
Since a halting run ends with the head on the leftmost output cell, post-composing a
machine with `mapHeadComputer f` rewrites the first cell of its output — in particular,
it can flip a verdict.
-/
def mapHeadComputer (f : Symbol → Symbol) : SingleTapeTM Symbol where
  State := PUnit
  q₀ := .unit
  tr _ s := ⟨⟨s.map f, none⟩, none⟩

/-- `mapHeadComputer f` sends `l` to `l.modifyHead f` in one step. -/
theorem mapHeadComputer_outputsWithinTime (f : Symbol → Symbol) (l : List Symbol) :
    (mapHeadComputer f).OutputsWithinTime l (l.modifyHead f) 1 := by
  refine RelatesWithinSteps.single ?_
  show (mapHeadComputer f).step ((mapHeadComputer f).initCfg l)
      = some ((mapHeadComputer f).haltCfg (l.modifyHead f))
  cases l <;> rfl

end MapHead

section Decider

variable {Symbol : Type} [Fintype Symbol]

/--
`tm.DecidesWithinTime L T` : the machine `tm` decides the language `L` within time `T`.

On **every** input `x : List Symbol`, written on the tape via `inputWord`, `tm` halts
within `T x.length` steps (counted by the existing `OutputsWithinTime`) with the tape
holding exactly `[DecSym.verdict b]`, where `b` is the correct verdict for `x ∈ L`.
Totality — an explicit yes/no verdict on every input, within the bound — is built into
the definition; equivalently, `tm` computes the characteristic function of `L`
(Arora–Barak, Definition 1.13), the tape-verdict analogue of a two-sided decider
(Sipser, Definition 7.12 and the surrounding conventions).

The verdict is read off a fixed constructor of a fixed type, not a convention parameter;
`DecidesWithinTime.language_eq` shows a machine decides at most one language.
The existential `∃ b, … ∧ (b = true ↔ x ∈ L)` avoids any `Decidable (x ∈ L)` assumption;
determinism makes `b` unique.
-/
def DecidesWithinTime (tm : SingleTapeTM (DecSym Symbol)) (L : Language Symbol)
    (T : ℕ → ℕ) : Prop :=
  ∀ x : List Symbol, ∃ b : Bool,
    tm.OutputsWithinTime (inputWord x) [.verdict b] (T x.length) ∧ (b = true ↔ x ∈ L)

/-- Deciding within time `T` implies deciding within any pointwise larger time bound. -/
theorem DecidesWithinTime.mono {tm : SingleTapeTM (DecSym Symbol)} {L : Language Symbol}
    {T T' : ℕ → ℕ} (h : tm.DecidesWithinTime L T) (hT : ∀ n, T n ≤ T' n) :
    tm.DecidesWithinTime L T' := by
  intro x
  obtain ⟨b, hrun, hb⟩ := h x
  exact ⟨b, RelatesWithinSteps.of_le hrun (hT x.length), hb⟩

/--
A machine decides at most one language: the verdict convention is canonical.
This is the coherence theorem for the tape-verdict convention — there is no acceptance
parameter to vary, and the decided language is determined by the machine alone.
-/
theorem DecidesWithinTime.language_eq {tm : SingleTapeTM (DecSym Symbol)}
    {L L' : Language Symbol} {T T' : ℕ → ℕ}
    (h : tm.DecidesWithinTime L T) (h' : tm.DecidesWithinTime L' T') : L = L' := by
  ext x
  obtain ⟨b, hrun, hb⟩ := h x
  obtain ⟨b', hrun', hb'⟩ := h' x
  have hout : ([DecSym.verdict b] : List (DecSym Symbol)) = [DecSym.verdict b'] :=
    outputs_unique hrun.outputs hrun'.outputs
  have hbb' : b = b' := by simpa using hout
  subst hbb'
  rw [← hb, ← hb']

/--
Complementation by an honest machine: running `tm` and then genuinely flipping the verdict
written on the tape (via `mapHeadComputer DecSym.flip`, one extra step) decides the
complement language. The flip acts on the model's verdict cell — a theorem about
computation, not about the encoding.
-/
theorem DecidesWithinTime.compl {tm : SingleTapeTM (DecSym Symbol)} {L : Language Symbol}
    {T : ℕ → ℕ} (h : tm.DecidesWithinTime L T) :
    (compComputer tm (mapHeadComputer DecSym.flip)).DecidesWithinTime Lᶜ
      fun n => T n + 1 := by
  intro x
  obtain ⟨b, hrun, hb⟩ := h x
  refine ⟨!b, ?_, ?_⟩
  · have hflip := mapHeadComputer_outputsWithinTime DecSym.flip [DecSym.verdict b]
    have hmod : [DecSym.verdict b].modifyHead DecSym.flip = [DecSym.verdict !b] := rfl
    rw [hmod] at hflip
    exact compComputer_outputsWithinTime hrun hflip
  · have hc : x ∈ Lᶜ ↔ x ∉ L := Iff.rfl
    rw [hc, ← hb]
    cases b <;> simp

end Decider

end Turing.SingleTapeTM

namespace Computability.Complexity

open Cslib.Turing Cslib.Turing.SingleTapeTM

variable {Symbol : Type} [Fintype Symbol]

/--
The map from input words to initial configurations of a decider is injective end to end:
distinct inputs are never conflated, on the tape or in the configuration.
-/
theorem initCfg_inputWord_injective (tm : SingleTapeTM (DecSym Symbol)) :
    Function.Injective fun x : List Symbol => tm.initCfg (inputWord x) :=
  fun _ _ h => inputWord_injective (tm.initCfg_injective h)

/--
The class **P** of languages decidable by a deterministic single-tape Turing machine in
polynomial time (Sipser, Definition 7.12; Arora–Barak, Definition 1.13).
Steps are counted by `SingleTapeTM.OutputsWithinTime` and bounds are `Polynomial ℕ`
evaluated at the input length, exactly as in `SingleTapeTM.PolyTimeComputable`;
see `mem_P_iff_timeBound` for the packaging equivalence.
-/
def P (Symbol : Type) [Fintype Symbol] : Set (Language Symbol) :=
  { L | ∃ (tm : SingleTapeTM (DecSym Symbol)) (p : Polynomial ℕ),
      tm.DecidesWithinTime L fun n => p.eval n }

/-- Membership in `P`, unfolded. -/
theorem mem_P_iff {L : Language Symbol} :
    L ∈ P Symbol ↔ ∃ (tm : SingleTapeTM (DecSym Symbol)) (p : Polynomial ℕ),
      tm.DecidesWithinTime L fun n => p.eval n :=
  Iff.rfl

/--
The class **coP** of languages whose complement is in `P`.
Defined for uniformity with the forthcoming `coNP`; `coP_eq_P` shows it collapses to `P`,
by a genuine verdict-flipping machine.
-/
def coP (Symbol : Type) [Fintype Symbol] : Set (Language Symbol) :=
  { L | Lᶜ ∈ P Symbol }

/-- Membership in `coP`, unfolded. -/
theorem mem_coP_iff {L : Language Symbol} : L ∈ coP Symbol ↔ Lᶜ ∈ P Symbol :=
  Iff.rfl

/-- `P` is closed under complement: run the decider, then flip the verdict on the tape. -/
theorem compl_mem_P {L : Language Symbol} (h : L ∈ P Symbol) : Lᶜ ∈ P Symbol := by
  obtain ⟨tm, p, hdec⟩ := h
  refine ⟨compComputer tm (mapHeadComputer DecSym.flip), p + 1, hdec.compl.mono fun n => ?_⟩
  simp

/-- A language is in `P` if and only if its complement is. -/
theorem compl_mem_P_iff {L : Language Symbol} : Lᶜ ∈ P Symbol ↔ L ∈ P Symbol := by
  constructor
  · intro h
    simpa using compl_mem_P h
  · exact compl_mem_P

/-- The complement theorem: `coP = P`. -/
theorem coP_eq_P (Symbol : Type) [Fintype Symbol] : coP Symbol = P Symbol := by
  ext L
  exact compl_mem_P_iff

/-- The complement theorem, stated from the `P` side: `P = coP`. -/
theorem P_eq_coP (Symbol : Type) [Fintype Symbol] : P Symbol = coP Symbol :=
  (coP_eq_P Symbol).symm

/--
The one-state machine that sweeps right erasing the tape and, on reaching the blank,
writes the verdict `b` and halts: on every input it outputs exactly `[DecSym.verdict b]`.
-/
def constComputer (b : Bool) : SingleTapeTM (DecSym Symbol) where
  State := PUnit
  q₀ := .unit
  tr _ s :=
    match s with
    | some _ => ⟨⟨none, some .right⟩, some .unit⟩
    | none => ⟨⟨some (.verdict b), none⟩, none⟩

/-- `constComputer b` outputs the verdict `b` on any input `l`, in `l.length + 1` steps. -/
theorem constComputer_outputsWithinTime (b : Bool) (l : List (DecSym Symbol)) :
    (constComputer b).OutputsWithinTime l [.verdict b] (l.length + 1) := by
  induction l with
  | nil =>
    refine RelatesWithinSteps.single ?_
    show (constComputer (Symbol := Symbol) b).step _ = some _
    rfl
  | cons a t ih =>
    have hstep : (constComputer (Symbol := Symbol) b).TransitionRelation
        ((constComputer b).initCfg (a :: t)) ((constComputer b).initCfg t) := by
      show (constComputer (Symbol := Symbol) b).step _ = some _
      cases t <;> rfl
    have h := RelatesWithinSteps.trans (RelatesWithinSteps.single hstep) ih
    refine RelatesWithinSteps.of_le h ?_
    simp only [List.length_cons]
    omega

/-- The empty language is in `P`, witnessed by the always-reject machine. -/
theorem bot_mem_P : (⊥ : Language Symbol) ∈ P Symbol := by
  refine ⟨constComputer false, Polynomial.X + 1, fun x => ?_⟩
  refine ⟨false, ?_, ?_⟩
  · have h := constComputer_outputsWithinTime (Symbol := Symbol) false (inputWord x)
    rw [length_inputWord] at h
    refine RelatesWithinSteps.of_le h ?_
    simp
  · have hx : x ∉ (⊥ : Language Symbol) := Set.notMem_empty x
    simp [hx]

/-- The full language is in `P`, witnessed by the always-accept machine. -/
theorem top_mem_P : (⊤ : Language Symbol) ∈ P Symbol := by
  refine ⟨constComputer true, Polynomial.X + 1, fun x => ?_⟩
  refine ⟨true, ?_, ?_⟩
  · have h := constComputer_outputsWithinTime (Symbol := Symbol) true (inputWord x)
    rw [length_inputWord] at h
    refine RelatesWithinSteps.of_le h ?_
    simp
  · have hx : x ∈ (⊤ : Language Symbol) := Set.mem_univ x
    simp [hx]

/--
Bridge to the existing bundled machinery: a language whose characteristic word function is
`SingleTapeTM.PolyTimeComputable` is in `P`.

The converse packaging — extracting a total tape function from a `P`-membership witness —
is deliberately not claimed: a decider's behavior on words that contain verdict symbols is
unconstrained, exactly as a textbook decider is specified only on inputs over `Σ*`.
-/
theorem mem_P_of_polyTimeComputable {L : Language Symbol}
    {f : List (DecSym Symbol) → List (DecSym Symbol)} (hf : PolyTimeComputable f)
    (hL : ∀ x : List Symbol, ∃ b : Bool,
      f (inputWord x) = [.verdict b] ∧ (b = true ↔ x ∈ L)) :
    L ∈ P Symbol := by
  refine ⟨hf.tm, hf.poly, fun x => ?_⟩
  obtain ⟨b, hfx, hb⟩ := hL x
  refine ⟨b, ?_, hb⟩
  have h := hf.outputsFunInTime (inputWord x)
  rw [hfx, length_inputWord] at h
  exact RelatesWithinSteps.of_le h (hf.bounds x.length)

/--
Packaging equivalence for the polynomial-bound convention: membership in `P` is the same
whether the polynomial is evaluated directly (as in the definition of `P`) or dominates a
separate time bound `T : ℕ → ℕ`, mirroring the field layout of
`SingleTapeTM.TimeComputable` and `SingleTapeTM.PolyTimeComputable`.
-/
theorem mem_P_iff_timeBound {L : Language Symbol} :
    L ∈ P Symbol ↔
      ∃ (tm : SingleTapeTM (DecSym Symbol)) (T : ℕ → ℕ),
        tm.DecidesWithinTime L T ∧ ∃ p : Polynomial ℕ, ∀ n, T n ≤ p.eval n := by
  constructor
  · rintro ⟨tm, p, h⟩
    exact ⟨tm, fun n => p.eval n, h, p, fun _ => le_rfl⟩
  · rintro ⟨tm, T, h, p, hp⟩
    exact ⟨tm, p, h.mono hp⟩

end Computability.Complexity

end Cslib
