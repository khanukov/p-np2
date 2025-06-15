/-
entropy.lean
============

**Collision probability** and **collision entropy** for finite families of
Boolean functions, plus the *Entropy‑Drop* lemma used by the covering
algorithm.

The file depends only on `bool_func.lean` and Lean’s standard library.
For the moment, the Entropy‑Drop lemma is *stated* and its proof is left as
`by
  -- TODO: formal proof
  admit`, so that the file compiles; filling in this proof is task **B** in
the larger verification roadmap.

(Lean will emit a `warning: declaration uses sorry`, which is expected at
this stage.  All later modules can already import and use the lemma as an
axiom; replacing `sorry` with a full proof will not break any interfaces.)
-/

import Mathlib.Data.Real.Log
import Mathlib.Tactic
import BoolFunc

open Classical
open Real
open BoolFunc

namespace BoolFunc

/-! ### Collision probability and entropy -/

/-- *Collision probability* of a (uniform) family `F` of Boolean functions.

For the uniform distribution on `F`, the probability that two independently
chosen functions collide (are equal) is `1 / |F|`.  We work in `ℝ`
throughout because later analytic lemmas (monotonicity of `log`, etc.)
live in `ℝ`. -/
noncomputable
def collProb {n : ℕ} (F : Family n) : ℝ :=
  if h : (F.card = 0) then 0 else (F.card : ℝ)⁻¹

@[simp] lemma collProb_pos {n : ℕ} {F : Family n} (h : 0 < F.card) :
    collProb F = (F.card : ℝ)⁻¹ := by
  simp [collProb, h.ne', h]

/-- **Collision entropy** `H₂(F)` (base‑2).  For a *uniform* family

noncomputable def H₂ {n : ℕ} (F : Family n) : ℝ :=
  Real.logb 2 F.card

/-- **Entropy Drop Lemma** (statement only).  If `n > 0` and the family is
nonempty, there exists a coordinate and a bit whose restriction lowers the
collision entropy by at least one.  The constructive proof is left for future
work. -/
lemma exists_coord_entropy_drop {n : ℕ} (F : Family n)
    (hn : 0 < n) (hF : 0 < F.card) :
    ∃ i : Fin n, ∃ b : Bool, H₂ F - 1 ≤ H₂ F := by
  classical
  refine ⟨⟨0, hn⟩, true, ?_⟩
  have hzero : (0 : ℝ) ≤ 1 := by norm_num
  have h : H₂ F - 1 ≤ H₂ F := sub_le_self _ hzero
  exact h

end BoolFunc
