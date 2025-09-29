import Pnp2.BoolFunc
import Pnp2.entropy
import Pnp2.Cover.Bounds
import Pnp2.Cover.Canonical
import Pnp2.bound

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
      (hn := by decide))

/--
The strengthened `buildCover` bound is definitionally the same as the
`coverFamily` bound.  This smoke test ensures the new lemma rewrites to concrete
numerals without additional manual algebra.
-/
example :
    (Cover2.buildCover (n := 6) (F := singletonFamily 6) 2
        (by
          rw [singleton_entropy 6]
          norm_num)).card ≤ Cover2.mBound 6 2 := by
  classical
  have hH : H₂ (singletonFamily 6) ≤ (2 : ℝ) := by
    rw [singleton_entropy 6]
    norm_num
  simpa using
    (Cover2.buildCover_card_le_mBound (n := 6) (F := singletonFamily 6)
      (h := 2) (hH := hH) (hn := by decide))

/--
Sanity checks for the explicit arithmetic lemma `two_pow_le_mBound`.  These
examples confirm that concrete instantiations of the guard produce true
inequalities.
-/
example : (2 : ℕ) ^ 10 ≤ Cover2.mBound 10 3 := by decide
example : (2 : ℕ) ^ 15 ≤ Cover2.mBound 15 4 := by decide
example : (2 : ℕ) ^ 20 ≤ Cover2.mBound 20 5 := by decide

/--
The formal Family Collision–Entropy Lemma works without the legacy guard
`n ≤ C ⋅ h`.  Instantiating it for the singleton family at
`n = Bound.n₀ 0 = 20 000` exercises the final statement and checks that the
resulting cover is bounded by the cubic truth-table bound `2^{3n + 2}`.
-/
example :
    ∃ Rset : Finset (Boolcube.Subcube (Bound.n₀ 0)),
      (∀ R ∈ Rset, ∀ g ∈ singletonFamily (Bound.n₀ 0),
          Boolcube.Subcube.monochromaticFor R g) ∧
      (∀ f ∈ singletonFamily (Bound.n₀ 0), ∀ x,
          f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
      Rset.card ≤ Nat.pow 2 (3 * Bound.n₀ 0 + 2) := by
  classical
  -- Abbreviate the dimension to keep subsequent rewrites readable.
  set n := Bound.n₀ 0
  -- The entropy bound is immediate for the singleton family.
  have hH : H₂ (singletonFamily n) ≤ (0 : ℝ) := by
    simpa [singleton_entropy] using (show (0 : ℝ) ≤ 0 from le_rfl)
  -- The hypotheses on the ambient dimension follow from the explicit formula.
  have hn_pos : 0 < n := by
    simpa [n, Bound.n₀]
  -- The exported theorem packages the full cover specification.
  simpa [n] using
    (Bound.family_collision_entropy_lemma
      (F := singletonFamily n)
      (h := 0)
      (hH := hH)
      (hn_pos := hn_pos))
