import Pnp2.BoolFunc
import Pnp2.entropy
import Pnp2.Cover.Bounds
import Pnp2.Cover.Canonical

open Classical
open BoolFunc
open Cover2

/-- Constant `false` Boolean function on `n` variables. -/
noncomputable def constFalse (n : ℕ) : BFunc n := fun _ => false

/-- Singleton family containing only the constant `false` function. -/
noncomputable def singletonFamily (n : ℕ) : Family n := {constFalse n}

lemma singleton_family_card (n : ℕ) :
    (singletonFamily n).card = 1 := by
  classical
  simp [singletonFamily]

lemma singleton_entropy (n : ℕ) :
    H₂ (singletonFamily n) = 0 := by
  classical
  simpa [singletonFamily]
    using H₂_card_one (F := singletonFamily n) (singleton_family_card n)

/--
For small parameters the canonical cover contains at most `2^n` rectangles.
This exercises the strengthened combinatorial bound without appealing to the
cardinality of the ambient subcube type.
-/
example :
    (Cover2.coverFamily (n := 6) (F := singletonFamily 6) (h := 2)
        (hH := by
          rw [singleton_entropy 6]
          norm_num)).card ≤ 2 ^ 6 := by
  classical
  -- Explicitly materialise the entropy guard once so it can be reused.
  have hH : H₂ (singletonFamily 6) ≤ (2 : ℝ) := by
    rw [singleton_entropy 6]
    norm_num
  -- Rephrase the goal in terms of `hH`; the proof term provided by the
  -- `by` block above is definitionally equal to the named hypothesis.
  change
      (Cover2.coverFamily (n := 6) (F := singletonFamily 6) (h := 2)
          (hH := hH)).card ≤ 2 ^ 6
  -- Now the strengthened combinatorial bound applies directly.
  simpa using
    (Cover2.coverFamily_spec_bound (n := 6) (h := 2) (F := singletonFamily 6)
      (hH := hH))

/--
The numeric guard `n ≤ 5 * h` upgrades the catalogue bound `2^n` to
`mBound n h`.  Instantiating the lemma at a concrete point checks that Lean can
rewrite the final inequality down to numerals.
-/
example :
    (Cover2.coverFamily (n := 6) (F := singletonFamily 6) (h := 2)
        (hH := by
          rw [singleton_entropy 6]
          norm_num)).card ≤ Cover2.mBound 6 2 := by
  classical
  -- As above, extract the entropy bound to an explicit name for reuse.
  have hH : H₂ (singletonFamily 6) ≤ (2 : ℝ) := by
    rw [singleton_entropy 6]
    norm_num
  -- Align the goal with the instance that uses the named hypothesis.
  change
      (Cover2.coverFamily (n := 6) (F := singletonFamily 6) (h := 2)
          (hH := hH)).card ≤ Cover2.mBound 6 2
  -- Finally appeal to the upgraded arithmetic inequality.
  simpa using
    (Cover2.coverFamily_card_le_mBound (n := 6) (h := 2)
      (F := singletonFamily 6)
      (hH := hH)
      (hn := by decide) (hlarge := by decide))

/--
Sanity checks for the explicit arithmetic lemma `two_pow_le_mBound`.  These
examples confirm that concrete instantiations of the guard produce true
inequalities.
-/
example : (2 : ℕ) ^ 10 ≤ Cover2.mBound 10 3 := by decide
example : (2 : ℕ) ^ 15 ≤ Cover2.mBound 15 4 := by decide
example : (2 : ℕ) ^ 20 ≤ Cover2.mBound 20 5 := by decide
