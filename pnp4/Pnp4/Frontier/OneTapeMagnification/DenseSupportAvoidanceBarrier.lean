import Pnp4.Frontier.OneTapeMagnification.LocalHSGToMCSP
import Pnp4.Frontier.OneTapeMagnification.SupportAvoidance
import Mathlib.Tactic

/-!
# Seed-length barrier for universal dense hitting

`LocalHSGToMCSP` only asks a generator to hit the dense acceptance predicate
of one fixed bounded-time one-tape machine.  It would be tempting to replace
that structured requirement by the much stronger assertion that the same
generator hits every predicate of density strictly above one half.

This file rules out that shortcut.  If `seedBits + 1 < 2 ^ n`, the complement
of the generator image is itself larger than half of the truth-table cube and
is missed by every seed.  Consequently a short-seed generator cannot hit all
dense truth-table predicates, independently of fixed-seed circuit locality.

The avoiding predicate depends on the generator and is not shown to be
computable by a small one-tape machine.  Thus the result is an exact
information-theoretic barrier, not a lower bound for the structured CHMY
acceptance class and not a construction of the missing HSG.
-/

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

open StreamingMagnification
open StreamingMagnification.TotalSearch

/-- Universal dense hitting for truth-table predicates.  The mainline needs
only one structured predicate; this deliberately stronger interface is used
to state the information-theoretic obstruction precisely. -/
def HitsEveryDenseTruthTablePredicate
    {n seedBits : Nat}
    (generator : FiniteBitTape seedBits → TruthTable n) : Prop :=
  ∀ predicate : TruthTable n → Prop,
    DenseAboveHalf n predicate →
      ∃ seed : FiniteBitTape seedBits, predicate (generator seed)

/-- If the image itself occupies strictly less than half of the table cube,
its complement is a dense predicate.  This is the sharp support-size form of
the obstruction; it does not overcount colliding seeds. -/
theorem avoidSupport_denseAboveHalf_of_image_space_lt_half
    {n seedBits : Nat}
    (generator : FiniteBitTape seedBits → TruthTable n)
    (hImage :
      (Finset.univ.image generator).card * 2 <
        Fintype.card (TruthTable n)) :
    DenseAboveHalf n
      (fun table => avoidSupport generator table = true) := by
  classical
  let witnesses : Finset (TruthTable n) :=
    Finset.univ.filter fun table => avoidSupport generator table = true
  have hExact :
      witnesses.card = Fintype.card (TruthTable n) -
        (Finset.univ.image generator).card := by
    simpa [witnesses] using card_avoidSupport_true_eq generator
  have hDenseCard :
      Fintype.card (TruthTable n) < witnesses.card * 2 := by
    omega
  refine ⟨witnesses, ?_, ?_⟩
  · simpa [truthTableSpace_card] using hDenseCard
  · intro table hTable
    exact (Finset.mem_filter.mp hTable).2

/-- If the seed universe has size less than half of the table universe, the
predicate avoiding the generator support has density strictly above one
half. -/
theorem avoidSupport_denseAboveHalf_of_seed_space_lt_half
    {n seedBits : Nat}
    (generator : FiniteBitTape seedBits → TruthTable n)
    (hCard :
      Fintype.card (FiniteBitTape seedBits) * 2 <
        Fintype.card (TruthTable n)) :
    DenseAboveHalf n
      (fun table => avoidSupport generator table = true) := by
  classical
  apply avoidSupport_denseAboveHalf_of_image_space_lt_half generator
  have hImageCard :
      (Finset.univ.image generator).card ≤
        Fintype.card (FiniteBitTape seedBits) := by
    simpa using
      (Finset.card_image_le :
        (Finset.univ.image generator).card ≤
          (Finset.univ : Finset (FiniteBitTape seedBits)).card)
  omega

/-- A one-bit seed-length deficit already makes the support complement dense:
`2^(seedBits)` is then strictly smaller than half of `2^(2^n)`. -/
theorem avoidSupport_denseAboveHalf_of_seedBits_succ_lt
    {n seedBits : Nat}
    (generator : FiniteBitTape seedBits → TruthTable n)
    (hSeedBits : seedBits + 1 < 2 ^ n) :
    DenseAboveHalf n
      (fun table => avoidSupport generator table = true) := by
  apply avoidSupport_denseAboveHalf_of_seed_space_lt_half generator
  rw [finiteSeedSpace_card, truthTableSpace_card]
  have hPower : 2 ^ (seedBits + 1) < 2 ^ (2 ^ n) :=
    Nat.pow_lt_pow_right (by decide : 1 < (2 : Nat)) hSeedBits
  simpa [pow_succ, Nat.mul_comm] using hPower

/-- No short-seed map can hit every predicate of density above one half.  The
counterexample is the explicit Boolean predicate avoiding its image. -/
theorem not_hitsEveryDenseTruthTablePredicate_of_seedBits_succ_lt
    {n seedBits : Nat}
    (generator : FiniteBitTape seedBits → TruthTable n)
    (hSeedBits : seedBits + 1 < 2 ^ n) :
    ¬ HitsEveryDenseTruthTablePredicate generator := by
  intro hHits
  have hDense :=
    avoidSupport_denseAboveHalf_of_seedBits_succ_lt generator hSeedBits
  rcases hHits
      (fun table => avoidSupport generator table = true) hDense with
    ⟨seed, hAccept⟩
  simp at hAccept

/-- Universal dense hitting forces the distinct generator image to cover at
least half of the truth-table cube.  In particular, collisions cannot be
hidden behind a large nominal seed space. -/
theorem image_covers_half_of_hitsEveryDenseTruthTablePredicate
    {n seedBits : Nat}
    (generator : FiniteBitTape seedBits → TruthTable n)
    (hHits : HitsEveryDenseTruthTablePredicate generator) :
    Fintype.card (TruthTable n) ≤
      (Finset.univ.image generator).card * 2 := by
  classical
  by_contra hHalf
  have hImage :
      (Finset.univ.image generator).card * 2 <
        Fintype.card (TruthTable n) := by
    omega
  have hDense :=
    avoidSupport_denseAboveHalf_of_image_space_lt_half generator hImage
  rcases hHits
      (fun table => avoidSupport generator table = true) hDense with
    ⟨seed, hAccept⟩
  simp at hAccept

/-- In bit-length form, universal dense hitting needs at least
`2^n - 1` seed bits: a sublinear-in-the-table-length seed cannot possibly
serve an unrestricted predicate class. -/
theorem truthTableLength_le_seedBits_succ_of_hitsEveryDense
    {n seedBits : Nat}
    (generator : FiniteBitTape seedBits → TruthTable n)
    (hHits : HitsEveryDenseTruthTablePredicate generator) :
    2 ^ n ≤ seedBits + 1 := by
  by_contra hLength
  have hSeedBits : seedBits + 1 < 2 ^ n := by omega
  exact
    (not_hitsEveryDenseTruthTablePredicate_of_seedBits_succ_lt
      generator hSeedBits) hHits

/-- Specialization to the repository's fixed-seed-DAG-local generator.  The
contradiction uses only seed length; `image_easy` cannot rescue universal
dense hitting. -/
theorem dagLocalGenerator_not_hitsEveryDenseTruthTablePredicate
    {n threshold : Nat}
    (generator : DAGLocalGenerator n threshold)
    (hSeedBits : generator.seedBits + 1 < 2 ^ n) :
    ¬ HitsEveryDenseTruthTablePredicate generator.generate :=
  not_hitsEveryDenseTruthTablePredicate_of_seedBits_succ_lt
    generator.generate hSeedBits

end OneTapeMagnification
end Frontier
end Pnp4
