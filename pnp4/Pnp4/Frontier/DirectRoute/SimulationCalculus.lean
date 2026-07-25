import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Logic.Relation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The simulation calculus: why every *direct* route to `P ≠ NP` stalls in the same place

This module is not about magnification, MCSP, or any reduction.  It is about the
**direct** attack: assume `P = NP`, compose known simulation theorems, and try to
contradict a hierarchy theorem.  That is indirect diagonalization, the only
family of techniques that has ever produced an unconditional separation of
determinism from nondeterminism (Paul–Pippenger–Szemerédi–Trotter, `NTIME[n] ≠
TIME[n]` for multitape machines).

The purpose here is to make the family itself a formal object, so that the
question "can this ever reach `P ≠ NP`?" becomes a theorem rather than folklore.

## The two non-relativizing resources

Only two structural facts about Turing machines survive oracle access, and every
direct result is built from them:

* **R1 — local checkability.** A time-`t` computation is a locally constrained
  tableau (Cook–Levin).  This is what makes `SAT` complete and what breaks under
  oracle queries, which are non-local.
* **R2 — space-efficient simulation of time.**  `TIME[t] ⊆ SPACE[t / log t]`
  (Hopcroft–Paul–Valiant 1975), improved to `TIME[t] ⊆ SPACE[√(t log t)]`
  (R. Williams, STOC 2025, best paper).  `TIME[t] ⊆ ATIME[t / log t]`
  (Dymond–Tompa 1985) and `TIME[t] ⊆ Σ₂TIME[o(t)]` (PPST 1983 / Tretkoff) are
  the bounded-alternation variants.

## The calculus

Resources are `(class, exponent)` pairs, exponents measured as powers of the
input length.  Arrows are the published simulations plus the consequences of the
assumption `P = NP` with `SAT ∈ DTIME[n^c]`:

| arrow | source |
|---|---|
| `dtime α → ntime α` | trivial |
| `ntime α → sigma 1 α` | trivial |
| `sigma j α → dtime (c^j · α)` | `P = NP` collapses `PH`; each level costs a factor `c` |
| `dtime α → dspace (α/2)` | Williams 2025 |
| `dtime α → dspace α` | Hopcroft–Paul–Valiant |
| `ntime α → dspace α` | trivial |
| `dtime α → sigma k ((1-δ)·α)` | the **speedup arrow**: PPST/Dymond–Tompa give this with `δ = 0` (logarithmic gain only) |

A refutation of the assumption means deriving `dtime α → dtime β` with `β < α`,
contradicting the deterministic time hierarchy.

## What is proved here

1. `dspace_sink` — space is a **sink**: once a derivation reaches `dspace`, it
   never returns to a time class.  This is why Williams' polynomial gain (the
   only polynomial gain known) cannot be cashed.
2. `exponent_monotone` — if `1 ≤ (1-δ)·c^k`, every derivation between time
   classes is non-decreasing in the exponent.  Hence no contradiction, hence the
   calculus cannot refute `P = NP`.
3. `contradiction_of_below_threshold` — conversely, if `(1-δ)·c^k < 1` the
   contradiction is derivable in two steps.  So the threshold is exact.
4. `fixed_gain_insufficient` — **the punchline.**  For every fixed alternation
   depth `k ≥ 1` and every fixed gain `δ < 1` there is an assumption exponent
   `c` at which the threshold holds.  Since `P = NP` only supplies *some*
   polynomial `c`, no speedup arrow with a fixed gain can ever close the loop.

## What this says about a new path

Reading (4) contrapositively: a direct route needs an arrow whose gain **grows
with `c`**, or a technique in which the assumption is used **additively** rather
than multiplicatively.  Indirect diagonalization is multiplicative by
construction — the assumed algorithm is applied to the whole computation, so its
exponent multiplies at every cycle.  The one known additive-cost template is the
*algorithmic method* (a faster-than-brute-force algorithm invoked once inside a
single nondeterministic guess), which is exactly the technique that produced
`NEXP ⊄ ACC⁰`.

This module does not prove `P ≠ NP` and does not claim any new separation.  It
proves that a precisely specified, published toolkit cannot produce one, and it
names the property a new tool must have.
-/

namespace Pnp4
namespace Frontier
namespace DirectRoute

/-- A complexity resource: a class together with a polynomial exponent. -/
inductive Resource where
  /-- `DTIME[n ^ α]`. -/
  | dtime (α : ℚ)
  /-- `NTIME[n ^ α]`. -/
  | ntime (α : ℚ)
  /-- `Σ_j TIME[n ^ α]`. -/
  | sigma (j : Nat) (α : ℚ)
  /-- `SPACE[n ^ α]`. -/
  | dspace (α : ℚ)
  deriving Repr

namespace Resource

/-- The exponent carried by a resource. -/
def exponent : Resource → ℚ
  | dtime α => α
  | ntime α => α
  | sigma _ α => α
  | dspace α => α

/-- Space resources, the sink of the calculus. -/
def IsSpace : Resource → Prop
  | dspace _ => True
  | _ => False

/-- Exponents are never negative along a legal derivation. -/
def Ok (X : Resource) : Prop := 0 ≤ X.exponent

end Resource

open Resource

/--
One simulation step.

`c` is the exponent of the assumed deterministic `SAT` algorithm
(`SAT ∈ DTIME[n ^ c]`, which is what `P = NP` supplies).  `k` and `δ` describe
the speedup arrow under consideration: `DTIME[n^α] ⊆ Σ_k TIME[n^((1-δ)α)]`.

Published instantiations: PPST/Tretkoff and Dymond–Tompa give this arrow with
`δ = 0` (their gain is a `log` factor, invisible at the level of exponents).
No arrow with `δ > 0` is known.
-/
inductive Step (c : ℚ) (k : Nat) (δ : ℚ) : Resource → Resource → Prop
  /-- Determinism is a special case of nondeterminism. -/
  | detToNondet (α : ℚ) : Step c k δ (dtime α) (ntime α)
  /-- One existential level. -/
  | ntimeToSigma (α : ℚ) : Step c k δ (ntime α) (sigma 1 α)
  /-- `P = NP` collapses the hierarchy; level `j` costs a factor `c ^ j`. -/
  | collapse (j : Nat) (α : ℚ) : Step c k δ (sigma j α) (dtime (c ^ j * α))
  /-- Williams 2025: `TIME[t] ⊆ SPACE[√(t log t)]`. -/
  | williams (α : ℚ) : Step c k δ (dtime α) (dspace (α / 2))
  /-- Hopcroft–Paul–Valiant, at the level of exponents. -/
  | hpv (α : ℚ) : Step c k δ (dtime α) (dspace α)
  /-- A nondeterministic machine can be simulated in its own time as space. -/
  | ntimeToSpace (α : ℚ) : Step c k δ (ntime α) (dspace α)
  /-- Padding, inside each class. -/
  | padDtime {α β : ℚ} : α ≤ β → Step c k δ (dtime α) (dtime β)
  /-- Padding, inside each class. -/
  | padNtime {α β : ℚ} : α ≤ β → Step c k δ (ntime α) (ntime β)
  /-- Padding, inside each class. -/
  | padSigma {j : Nat} {α β : ℚ} : α ≤ β → Step c k δ (sigma j α) (sigma j β)
  /-- Padding, inside each class. -/
  | padSpace {α β : ℚ} : α ≤ β → Step c k δ (dspace α) (dspace β)
  /-- The speedup arrow. -/
  | speedup (α : ℚ) : Step c k δ (dtime α) (sigma k ((1 - δ) * α))

/-- Derivability: reflexive-transitive closure of `Step`. -/
abbrev Derives (c : ℚ) (k : Nat) (δ : ℚ) : Resource → Resource → Prop :=
  Relation.ReflTransGen (Step c k δ)

/-!
### Space is a sink
-/

lemma isSpace_of_step {c : ℚ} {k : Nat} {δ : ℚ} {X Y : Resource}
    (h : Step c k δ X Y) (hX : X.IsSpace) : Y.IsSpace := by
  cases h <;> simp [Resource.IsSpace] at hX ⊢

/--
**Space is a sink.**  Once a derivation enters `SPACE`, it stays there.

This is the formal reason the only *polynomial* gain in the toolkit
(Williams 2025, `α ↦ α/2`) cannot be used: there is no arrow back to a time
class, and a contradiction must be with a time hierarchy.
-/
theorem dspace_sink {c : ℚ} {k : Nat} {δ : ℚ} {X Y : Resource}
    (h : Derives c k δ X Y) (hX : X.IsSpace) : Y.IsSpace := by
  induction h with
  | refl => exact hX
  | tail _ hstep ih => exact isSpace_of_step hstep ih

/-!
### The monotone valuation
-/

/--
Potential of a resource: an alternation level `j` is worth a factor `c ^ j`,
because collapsing it under `P = NP` costs exactly that.
-/
def val (c : ℚ) : Resource → ℚ
  | dtime α => α
  | ntime α => α
  | sigma j α => c ^ j * α
  | dspace _ => 0

lemma ok_of_step {c : ℚ} {k : Nat} {δ : ℚ} {X Y : Resource}
    (hc : 1 ≤ c) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (h : Step c k δ X Y) (hX : X.Ok) : Y.Ok := by
  have hc0 : (0 : ℚ) ≤ c := le_trans zero_le_one hc
  cases h with
  | detToNondet α => simpa [Resource.Ok, Resource.exponent] using hX
  | ntimeToSigma α => simpa [Resource.Ok, Resource.exponent] using hX
  | collapse j α =>
      have hα : 0 ≤ α := hX
      have : (0 : ℚ) ≤ c ^ j := pow_nonneg hc0 j
      simpa [Resource.Ok, Resource.exponent] using mul_nonneg this hα
  | williams α =>
      have hα : 0 ≤ α := hX
      simpa [Resource.Ok, Resource.exponent] using by linarith
  | hpv α => simpa [Resource.Ok, Resource.exponent] using hX
  | ntimeToSpace α => simpa [Resource.Ok, Resource.exponent] using hX
  | padDtime hab => exact le_trans hX hab
  | padNtime hab => exact le_trans hX hab
  | padSigma hab => exact le_trans hX hab
  | padSpace hab => exact le_trans hX hab
  | speedup α =>
      have hα : 0 ≤ α := hX
      have h1 : (0 : ℚ) ≤ 1 - δ := by linarith
      simpa [Resource.Ok, Resource.exponent] using mul_nonneg h1 hα

/--
Every non-space step is non-decreasing in potential, provided the speedup gain
does not beat the cost of collapsing `k` alternation levels.
-/
lemma val_mono_of_step {c : ℚ} {k : Nat} {δ : ℚ} {X Y : Resource}
    (hc : 1 ≤ c) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hthr : 1 ≤ (1 - δ) * c ^ k)
    (h : Step c k δ X Y) (hX : X.Ok) (hY : ¬ Y.IsSpace) :
    val c X ≤ val c Y := by
  have hc0 : (0 : ℚ) ≤ c := le_trans zero_le_one hc
  cases h with
  | detToNondet α => simp [val]
  | ntimeToSigma α =>
      have hα : 0 ≤ α := hX
      have : α ≤ c * α := le_mul_of_one_le_left hα hc
      simpa [val, pow_one] using this
  | collapse j α => simp [val]
  | williams α => simp [Resource.IsSpace] at hY
  | hpv α => simp [Resource.IsSpace] at hY
  | ntimeToSpace α => simp [Resource.IsSpace] at hY
  | padDtime hab => simpa [val] using hab
  | padNtime hab => simpa [val] using hab
  | @padSigma j α β hab =>
      have : (0 : ℚ) ≤ c ^ j := pow_nonneg hc0 j
      simpa [val] using mul_le_mul_of_nonneg_left hab this
  | padSpace hab => simp [Resource.IsSpace] at hY
  | speedup α =>
      have hα : 0 ≤ α := hX
      have hmul : 1 * α ≤ ((1 - δ) * c ^ k) * α :=
        mul_le_mul_of_nonneg_right hthr hα
      have hgoal : val c (sigma k ((1 - δ) * α)) = ((1 - δ) * c ^ k) * α := by
        show c ^ k * ((1 - δ) * α) = ((1 - δ) * c ^ k) * α
        ring
      have hlhs : val c (dtime α) = α := rfl
      rw [hlhs, hgoal]
      linarith

/--
**No derivable speedup.**

Under the threshold `1 ≤ (1-δ)·c^k`, every derivation between time-like
resources is non-decreasing in potential.  In particular no derivation
`DTIME[n^α] ⊆ DTIME[n^β]` with `β < α` exists, so the deterministic time
hierarchy is never contradicted and the calculus cannot refute the assumption
`SAT ∈ DTIME[n^c]`.
-/
theorem val_monotone {c : ℚ} {k : Nat} {δ : ℚ}
    (hc : 1 ≤ c) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hthr : 1 ≤ (1 - δ) * c ^ k)
    {X Y : Resource} (h : Derives c k δ X Y) (hX : X.Ok) (hY : ¬ Y.IsSpace) :
    val c X ≤ val c Y := by
  induction h with
  | refl => exact le_refl _
  | @tail Z W hZ hstep ih =>
      have hZok : Z.Ok := by
        clear hstep ih
        induction hZ with
        | refl => exact hX
        | tail _ hs ih2 => exact ok_of_step hc hδ0 hδ1 hs ih2
      have hZnotSpace : ¬ Z.IsSpace := by
        intro hZs
        exact hY (isSpace_of_step hstep hZs)
      exact le_trans (ih hZnotSpace) (val_mono_of_step hc hδ0 hδ1 hthr hstep hZok hY)

/--
The consequence in the form a proof strategy cares about: no exponent decrease
between deterministic time classes.
-/
theorem exponent_monotone {c : ℚ} {k : Nat} {δ : ℚ}
    (hc : 1 ≤ c) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hthr : 1 ≤ (1 - δ) * c ^ k)
    {α β : ℚ} (hα : 0 ≤ α)
    (h : Derives c k δ (dtime α) (dtime β)) :
    α ≤ β := by
  have := val_monotone hc hδ0 hδ1 hthr h hα (by simp [Resource.IsSpace])
  simpa [val] using this

/-!
### The threshold is exact
-/

/--
Below the threshold the contradiction is immediate: speed up, then collapse.

This is the shape every indirect diagonalization has, and it shows the criterion
`(1-δ)·c^k < 1` is not an artefact of the potential function.
-/
theorem contradiction_of_below_threshold {c : ℚ} {k : Nat} {δ : ℚ}
    (hlow : (1 - δ) * c ^ k < 1) {α : ℚ} (hα : 0 < α) :
    ∃ β : ℚ, β < α ∧ Derives c k δ (dtime α) (dtime β) := by
  refine ⟨c ^ k * ((1 - δ) * α), ?_, ?_⟩
  · have heq : c ^ k * ((1 - δ) * α) = ((1 - δ) * c ^ k) * α := by ring
    have hlt : ((1 - δ) * c ^ k) * α < 1 * α := mul_lt_mul_of_pos_right hlow hα
    rw [heq]
    linarith
  · exact Relation.ReflTransGen.head (Step.speedup α)
      (Relation.ReflTransGen.single (Step.collapse k ((1 - δ) * α)))

/-!
### The punchline
-/

/--
**A fixed gain is never enough.**

For every alternation depth `k ≥ 1` and every fixed speedup gain `δ < 1` there
is an assumption exponent `c ≥ 1` at which the threshold `1 ≤ (1-δ)·c^k` holds,
and therefore (by `exponent_monotone`) at which the calculus derives no
contradiction whatsoever.

`P = NP` supplies only *some* polynomial exponent `c`; a proof must refute the
assumption for **all** `c`.  So no speedup arrow with a fixed gain can close the
loop, no matter how large the gain.

The published arrows are the case `δ = 0` (Paul–Pippenger–Szemerédi–Trotter,
Dymond–Tompa: the gain is a `log` factor, invisible in the exponent), for which
the threshold holds at every `c ≥ 1`.  This is exactly why `PPST` separates
`NTIME[n]` from `TIME[n]` — the case `c = 1` — and stops there.
-/
theorem fixed_gain_insufficient (k : Nat) (hk : 1 ≤ k) (δ : ℚ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    ∃ c : ℚ, 1 ≤ c ∧ 1 ≤ (1 - δ) * c ^ k := by
  have hpos : (0 : ℚ) < 1 - δ := by linarith
  refine ⟨1 / (1 - δ), ?_, ?_⟩
  · rw [le_div_iff₀ hpos]; linarith
  · have hpow : (1 / (1 - δ)) ^ k = 1 / (1 - δ) ^ k := by
      rw [div_pow, one_pow]
    rw [hpow]
    have hbase : (0 : ℚ) < (1 - δ) ^ k := pow_pos hpos k
    rw [mul_one_div, le_div_iff₀ hbase, one_mul]
    calc (1 - δ) ^ k ≤ (1 - δ) ^ 1 :=
          pow_le_pow_of_le_one (le_of_lt hpos) (by linarith) hk
      _ = 1 - δ := pow_one _

/--
Restatement of `fixed_gain_insufficient` as the requirement a new tool has to
meet: the gain must depend on `c`, i.e. the simulation must get *better* as the
assumed algorithm gets *worse*.

No known simulation has that shape, and the reason is structural: indirect
diagonalization applies the assumed algorithm to the whole computation, so its
exponent enters multiplicatively.  A technique in which the assumption is used
once — inside a single nondeterministic guess, as in the algorithmic method —
enters additively instead, and is therefore not covered by this no-go.
-/
def NewToolRequirement : Prop :=
  ∀ c : ℚ, 1 ≤ c → ∃ (k : Nat) (δ : ℚ), 0 ≤ δ ∧ δ ≤ 1 ∧ (1 - δ) * c ^ k < 1

/-- A tool meeting the requirement does refute the assumption at every `c`. -/
theorem refutation_of_newToolRequirement (h : NewToolRequirement)
    (c : ℚ) (hc : 1 ≤ c) {α : ℚ} (hα : 0 < α) :
    ∃ (k : Nat) (δ : ℚ) (β : ℚ), β < α ∧ Derives c k δ (dtime α) (dtime β) := by
  obtain ⟨k, δ, _, _, hlow⟩ := h c hc
  obtain ⟨β, hβ, hder⟩ := contradiction_of_below_threshold (k := k) (δ := δ) hlow hα
  exact ⟨k, δ, β, hβ, hder⟩

end DirectRoute
end Frontier
end Pnp4
