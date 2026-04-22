import Complexity.PpolyFormula_from_PpolyDAG_FixedSlice
import LowerBounds.FailedRoute_FixedSliceSupportHalfCore
import LowerBounds.SingletonDensityContradiction
import Magnification.LocalityProvider_Partial
import Magnification.FinalResultMainline

/-!
# Formula Support Bounds Falsifiability — Regression Test

Formalizes the full two-probe audit recorded in
`outputs/formula-support-bounds-falsifiability-audit.md` (commit
`d8a7753`) as in-project Lean proofs.  The audit showed that
`Magnification.FormulaSupportRestrictionBoundsPartial` is formally
INCONSISTENT with already-proven fixed-slice infrastructure — any
theorem depending on it is ex falso rather than genuine progress
toward an unconditional `NP ≠ P/poly`.

This file makes that inconsistency an in-project theorem so any future
edit that breaks the audit (or accidentally relies on the predicate in
a new context) trips a regression.

## Probe 1 — from fixed-slice `PpolyDAG`

Combined with a fixed-slice `PpolyDAG` witness, `FormulaSupportRestrictionBoundsPartial`
yields `False` — via the existing DAG→Formula bridge plus the
existing support-bounds consumer
`false_of_abstractGapTargetedPayload_of_supportBounds`.

## Probe 2/3 — unconditional `False` via truth-table hardwiring

For ANY Boolean function `f : Bitstring n → Bool`, there exists a
`FormulaCircuit n` whose `eval` agrees with `f`.  The construction is
recursive on `n`: at each level, split on input bit 0 and combine the
two sub-formulas with an `if/else` pattern (OR of two ANDs).  The
resulting `ttFormula f` is a concrete `FormulaCircuit n` for which
`ttFormula_eval : ∀ x, eval (ttFormula f) x = f x`.

Instantiating this at `n := partialInputLen p` with
`f := gapPartialMCSP_Language p (partialInputLen p)` yields a
`PpolyFormula (gapPartialMCSP_Language p)` (by wrapping in a family
that's `FormulaCircuit.const false` off the slice).  Combined with
Probe 1, this removes the `PpolyDAG` hypothesis and produces
`hBounds → False` unconditionally.

## Consequences (applies to the "active final line" in
`Magnification/FinalResultMainline.lean`)

Every theorem whose statement includes `hBounds :
FormulaSupportRestrictionBoundsPartial` in its hypotheses is
ex-falso: it vacuously "concludes" anything, including any NP-related
statement, without logical force.  Until the predicate is replaced
by a pipeline-restricted version (see
`pnp3/Docs/PhaseI_Verifier_Design.md` session 55 entry for the
migration plan), any such theorem should NOT be interpreted as
progress toward unconditionality.
-/

namespace Pnp3
namespace Tests
namespace FormulaSupportBoundsFalsifiabilityProbe

open ComplexityInterfaces
open Models
open LowerBounds

/-! ### Probe 1 (unchanged from session 55): from fixed-slice PpolyDAG -/

/-- **Regression lemma (Probe 1 from the audit)**: assuming
`FormulaSupportRestrictionBoundsPartial`, the fixed-slice language
`gapPartialMCSP_Language p` is NOT in `PpolyDAG`. -/
theorem fixedSlice_not_PpolyDAG_of_FormulaSupportRestrictionBoundsPartial
    {p : GapPartialMCSPParams}
    (hBounds : Magnification.FormulaSupportRestrictionBoundsPartial) :
    ¬ ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language p) := by
  intro hDag
  classical
  have hFormula :
      ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p) :=
    Complexity.ppolyFormula_of_ppolyDAG_gapPartialMCSP_fixedSlice p hDag
  have hPkg :
      Nonempty (AbstractGapTargetedSingletonDensityPayload p) :=
    abstractGapTargetedSingletonDensityPayload_of_dag hDag
  rcases hPkg with ⟨pkg⟩
  exact false_of_abstractGapTargetedPayload_of_supportBounds
    pkg hBounds hFormula

theorem false_of_FormulaSupportBounds_and_fixedSlice_PpolyDAG
    {p : GapPartialMCSPParams}
    (hBounds : Magnification.FormulaSupportRestrictionBoundsPartial)
    (hDag : ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language p)) :
    False :=
  fixedSlice_not_PpolyDAG_of_FormulaSupportRestrictionBoundsPartial
    hBounds hDag

/-! ### Probe 2: truth-table hardwiring — any Boolean function has a `FormulaCircuit`

We need a `FormulaCircuit n` computing any given `f : Bitstring n → Bool`.
Build it recursively on `n`: decompose `f` by the first input bit and
combine two subformulas with an `if/else` structure.

The recursion uses `Fin.succ` to shift indices when lifting subformulas
from width `k` to width `k + 1`. -/

/-- Shift all input indices in a `FormulaCircuit` by a user-supplied
rename function.  Used to lift subformulas to a wider input alphabet. -/
def FormulaCircuit.rename {m n : Nat} (σ : Fin m → Fin n) :
    FormulaCircuit m → FormulaCircuit n
  | .const b => .const b
  | .input i => .input (σ i)
  | .not c => .not (FormulaCircuit.rename σ c)
  | .and c1 c2 => .and (FormulaCircuit.rename σ c1) (FormulaCircuit.rename σ c2)
  | .or c1 c2 => .or (FormulaCircuit.rename σ c1) (FormulaCircuit.rename σ c2)

theorem FormulaCircuit.eval_rename {m n : Nat} (σ : Fin m → Fin n)
    (c : FormulaCircuit m) (x : Bitstring n) :
    FormulaCircuit.eval (FormulaCircuit.rename σ c) x =
      FormulaCircuit.eval c (fun i => x (σ i)) := by
  induction c with
  | const b => rfl
  | input i => rfl
  | not c ih => simp [FormulaCircuit.rename, FormulaCircuit.eval, ih]
  | and c1 c2 ih1 ih2 =>
    simp [FormulaCircuit.rename, FormulaCircuit.eval, ih1, ih2]
  | or c1 c2 ih1 ih2 =>
    simp [FormulaCircuit.rename, FormulaCircuit.eval, ih1, ih2]

/-- **Truth-table formula**: for any `f : Bitstring n → Bool`, build a
`FormulaCircuit n` whose `eval` agrees with `f`.  Recursive on `n`. -/
def ttFormula : ∀ {n : Nat}, (Bitstring n → Bool) → FormulaCircuit n
  | 0, f => FormulaCircuit.const (f (fun i => Fin.elim0 i))
  | (n + 1), f =>
    let f0 : Bitstring n → Bool := fun x => f (Fin.cases false x)
    let f1 : Bitstring n → Bool := fun x => f (Fin.cases true x)
    let c0 : FormulaCircuit n := ttFormula f0
    let c1 : FormulaCircuit n := ttFormula f1
    let c0' : FormulaCircuit (n + 1) := FormulaCircuit.rename Fin.succ c0
    let c1' : FormulaCircuit (n + 1) := FormulaCircuit.rename Fin.succ c1
    -- (¬ x₀ ∧ c0') ∨ (x₀ ∧ c1')
    FormulaCircuit.or
      (FormulaCircuit.and
        (FormulaCircuit.not (FormulaCircuit.input ⟨0, Nat.zero_lt_succ _⟩))
        c0')
      (FormulaCircuit.and
        (FormulaCircuit.input ⟨0, Nat.zero_lt_succ _⟩)
        c1')

/-- Correctness of `ttFormula`: `(ttFormula f).eval x = f x` for all `x`. -/
theorem ttFormula_eval : ∀ {n : Nat} (f : Bitstring n → Bool) (x : Bitstring n),
    FormulaCircuit.eval (ttFormula f) x = f x
  | 0, f, x => by
    -- x : Bitstring 0 = Fin 0 → Bool is the unique empty function.
    show f (fun i => Fin.elim0 i) = f x
    congr 1
    funext i
    exact Fin.elim0 i
  | (n + 1), f, x => by
    classical
    -- Unfold ttFormula into its or/and/not/input structure.
    show FormulaCircuit.eval (FormulaCircuit.or
            (FormulaCircuit.and
              (FormulaCircuit.not (FormulaCircuit.input ⟨0, Nat.zero_lt_succ _⟩))
              (FormulaCircuit.rename Fin.succ (ttFormula (fun y : Bitstring n =>
                f (Fin.cases false y)))))
            (FormulaCircuit.and
              (FormulaCircuit.input ⟨0, Nat.zero_lt_succ _⟩)
              (FormulaCircuit.rename Fin.succ (ttFormula (fun y : Bitstring n =>
                f (Fin.cases true y)))))) x = f x
    simp only [FormulaCircuit.eval, FormulaCircuit.eval_rename]
    -- Apply IH at width n:
    have ih0 := ttFormula_eval (fun y : Bitstring n => f (Fin.cases false y))
                 (fun i => x (Fin.succ i))
    have ih1 := ttFormula_eval (fun y : Bitstring n => f (Fin.cases true y))
                 (fun i => x (Fin.succ i))
    rw [ih0, ih1]
    -- Key: `Fin.cases (x 0) (x ∘ Fin.succ) = x` as functions `Fin (n+1) → Bool`.
    have hx_eq : ∀ (b : Bool),
        x ⟨0, Nat.zero_lt_succ _⟩ = b →
          (Fin.cases (n := n) b (fun i => x (Fin.succ i)) : Bitstring (n + 1)) = x := by
      intro b hb
      funext i
      induction i using Fin.cases with
      | zero =>
        show b = x ⟨0, Nat.zero_lt_succ _⟩
        exact hb.symm
      | succ j =>
        show (fun i => x (Fin.succ i)) j = x (Fin.succ j)
        rfl
    -- Case split on x 0.
    cases hx0 : x ⟨0, Nat.zero_lt_succ _⟩ with
    | false =>
      simp only [hx0, Bool.not_false, Bool.true_and, Bool.false_and, Bool.or_false]
      rw [hx_eq false hx0]
    | true =>
      simp only [hx0, Bool.not_true, Bool.false_and, Bool.true_and, Bool.false_or]
      rw [hx_eq true hx0]

/-! ### Probe 2: fixed-slice `gapPartialMCSP_Language ∈ PpolyFormula` (truth-table hardwiring) -/

/-- Size of any `FormulaCircuit` is at least 1. -/
private theorem formula_size_pos {n : Nat} (c : FormulaCircuit n) :
    1 ≤ FormulaCircuit.size c := by
  induction c with
  | const _ => exact Nat.le_refl 1
  | input _ => exact Nat.le_refl 1
  | not c ih => show 1 ≤ FormulaCircuit.size c + 1; omega
  | and c1 c2 ih1 _ =>
    show 1 ≤ FormulaCircuit.size c1 + FormulaCircuit.size c2 + 1
    omega
  | or c1 c2 ih1 _ =>
    show 1 ≤ FormulaCircuit.size c1 + FormulaCircuit.size c2 + 1
    omega

/-- **Probe 2 from the audit**: fixed-slice `gapPartialMCSP_Language p`
admits a `PpolyFormula` witness via truth-table hardwiring.  The
witness uses `ttFormula` at the single relevant input length
`partialInputLen p` and `FormulaCircuit.const false` elsewhere. -/
theorem fixedSlice_gapPartialMCSP_in_PpolyFormula
    (p : GapPartialMCSPParams) :
    ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p) := by
  classical
  let n₀ := Models.partialInputLen p
  let c₀ : FormulaCircuit n₀ := ttFormula (gapPartialMCSP_Language p n₀)
  let c₀_size : Nat := FormulaCircuit.size c₀
  have hc₀_pos : 1 ≤ c₀_size := formula_size_pos c₀
  refine ⟨{
    polyBound := fun m => if m = n₀ then c₀_size else 1
    polyBound_poly := ?_
    family := fun m =>
      if hm : m = n₀ then
        (hm ▸ c₀ : FormulaCircuit m)
      else
        FormulaCircuit.const false
    family_size_le := ?_
    correct := ?_
  }, trivial⟩
  · -- polyBound_poly: ∃ c, ∀ n, polyBound n ≤ n ^ c + c.
    refine ⟨c₀_size, ?_⟩
    intro m
    by_cases hm : m = n₀
    · simp [hm]
    · simp [hm]
      -- Need: 1 ≤ m ^ c₀_size + c₀_size.  Since c₀_size ≥ 1:
      exact Nat.le_trans hc₀_pos (Nat.le_add_left _ _)
  · -- family_size_le: ∀ m, (family m).size ≤ polyBound m.
    intro m
    by_cases hm : m = n₀
    · subst hm
      simp [c₀_size]
    · simp [hm, FormulaCircuit.size]
  · -- correct: ∀ m x, eval (family m) x = gapPartialMCSP_Language p m x.
    intro m x
    by_cases hm : m = n₀
    · subst hm
      simp only [dif_pos rfl]
      -- family m = c₀, so eval c₀ x = ttFormula_eval ... gives language value.
      show FormulaCircuit.eval c₀ x = gapPartialMCSP_Language p n₀ x
      exact ttFormula_eval (gapPartialMCSP_Language p n₀) x
    · simp only [dif_neg hm]
      -- family m = const false; need gapPartialMCSP_Language p m x = false when m ≠ n₀.
      -- Off-slice, the language is defined by `dite` no-branch which returns `false`.
      have hm' : ¬ m = Models.partialInputLen p := hm
      have hLang : gapPartialMCSP_Language p m x = false := by
        unfold gapPartialMCSP_Language
        exact dif_neg hm'
      simp [FormulaCircuit.eval, hLang]

/-! ### Probe 3: unconditional `hBounds → False` -/

/-- **Unconditional regression lemma (Probe 3 from the audit)**:
`FormulaSupportRestrictionBoundsPartial` alone (with no other
hypothesis) derives `False`, via Probe 2 (truth-table hardwiring
produces a `PpolyFormula` witness) + existing infrastructure
(`abstractGapTargetedSingletonDensityPayload_of_internal_provider` +
`false_of_abstractGapTargetedPayload_of_supportBounds`).

**Since `False` is derivable from the predicate alone, every theorem
consuming it has vacuous conclusion and is NOT a step toward
unconditional `NP ⊄ P/poly`.** -/
theorem false_of_FormulaSupportRestrictionBoundsPartial
    (p : GapPartialMCSPParams)
    (hBounds : Magnification.FormulaSupportRestrictionBoundsPartial) :
    False := by
  classical
  have hFormula : ComplexityInterfaces.PpolyFormula (gapPartialMCSP_Language p) :=
    fixedSlice_gapPartialMCSP_in_PpolyFormula p
  have hPkg :
      Nonempty (AbstractGapTargetedSingletonDensityPayload p) :=
    abstractGapTargetedSingletonDensityPayload_of_internal_provider hFormula
  rcases hPkg with ⟨pkg⟩
  exact false_of_abstractGapTargetedPayload_of_supportBounds
    pkg hBounds hFormula

/-! ### Probe 4: the multi-switching contract is ALSO inconsistent

The active final line `NP_not_subset_PpolyFormula_final` routes via
`hMag.switching.multiswitching : FormulaSupportBoundsFromMultiSwitchingContract`,
which discharges `FormulaSupportRestrictionBoundsPartial` via
`formula_support_bounds_from_multiswitching`.  Since Probe 3 proves
`FormulaSupportRestrictionBoundsPartial → False`, the multi-switching
contract is ALSO inconsistent in the current formalization: any call
site that takes `hMS` as a hypothesis is ex-falso.

**Implication for migration**: replacing `FormulaSupportRestrictionBoundsPartial`
alone is NOT sufficient.  The `FormulaSupportBoundsFromMultiSwitchingContract`
structure ALSO quantifies universally over `hFormula` and packages the
same false support-bounds claim.  Both must be reformulated to take
AC0 provenance data as INPUTS rather than PROMISING AC0-like bounds
for arbitrary formulas. -/

/-- **Probe 4**: `FormulaSupportBoundsFromMultiSwitchingContract` is
inconsistent — assuming it (without any other hypothesis) derives
`False`.  Direct consequence of Probe 3 + the existing derivation
`formula_support_bounds_from_multiswitching`. -/
theorem false_of_FormulaSupportBoundsFromMultiSwitchingContract
    (p : GapPartialMCSPParams)
    (hMS : Magnification.AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract) :
    False :=
  false_of_FormulaSupportRestrictionBoundsPartial p
    (Magnification.formula_support_bounds_from_multiswitching hMS)

/-- **Probe 5 — the "active final line" is ex-falso**:
`Magnification.MagnificationAssumptions` contains an `hMS` field of
type `FormulaSupportBoundsFromMultiSwitchingContract`, which by
Probe 4 is already inconsistent.  Therefore the top-level
`NP_not_subset_PpolyFormula_final` consuming `hMag : MagnificationAssumptions`
is ex-falso: for every non-empty `GapPartialMCSPParams p`, assuming
`hMag` yields `False`.

This directly shows that the final theorem's conclusion
`ComplexityInterfaces.NP_not_subset_PpolyFormula` is vacuous under
the current formalization. -/
theorem false_of_MagnificationAssumptions
    (p : GapPartialMCSPParams)
    (hMag : Magnification.MagnificationAssumptions) :
    False :=
  false_of_FormulaSupportBoundsFromMultiSwitchingContract p
    hMag.switching.multiswitching

/-- **Probe 6 — direct vacuity of the top-level final statement**:
`NP_not_subset_PpolyFormula_final hMag n hn` is provable *by ex falso*
given any `GapPartialMCSPParams` — the ex-falso bypass is
`false_of_MagnificationAssumptions`.

In other words, the top-level claim derives from vacuous assumptions.
Downstream code that reads the final theorem's conclusion
`NP_not_subset_PpolyFormula` should NOT consider it evidence toward
unconditional `NP ⊄ P/poly` until `FormulaSupportBoundsFromMultiSwitchingContract`
is replaced by a non-vacuous, AC0-provenance-restricted contract.

The construction simply derives `False` from `hMag` (via Probe 5) and
then uses `False.elim` to produce the conclusion. -/
theorem NP_not_subset_PpolyFormula_final_via_ex_falso
    (p : GapPartialMCSPParams)
    (hMag : Magnification.MagnificationAssumptions)
    (n : Nat) (_hn : hMag.antiChecker.asymptotic.N0 ≤ n) :
    ComplexityInterfaces.NP_not_subset_PpolyFormula :=
  False.elim (false_of_MagnificationAssumptions p hMag)

end FormulaSupportBoundsFalsifiabilityProbe
end Tests
end Pnp3
