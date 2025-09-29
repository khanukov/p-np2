import Pnp2.Cover.Measure
import Pnp2.Cover.Uncovered

open Classical
open Cover2
open BoolFunc (Family BFunc)
open Boolcube (Subcube)
open Finset

set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace Cover2Tests

/-- Trivial family used to sanity-check the lexicographic measure helpers. -/
@[simp] def emptyFamily (n : ℕ) : Family n := (∅ : Finset (BFunc n))

/-- Trivial rectangle set for the tests in this file. -/
@[simp] def emptyRectangles (n : ℕ) : Finset (Subcube n) := (∅ : Finset (Subcube n))

@[simp] lemma emptyFamily_allCovered {n : ℕ} :
    AllOnesCovered (n := n) (emptyFamily n) (emptyRectangles n) := by
  intro f hf
  simpa using hf

example {n : ℕ} :
    supportMass (n := n) (F := emptyFamily n) (Rset := emptyRectangles n) = 0 := by
  classical
  simpa using
    (supportMass_eq_zero_of_allCovered (n := n)
      (F := emptyFamily n) (Rset := emptyRectangles n) emptyFamily_allCovered)

example {n h : ℕ} :
    entropySurplus (n := n) (F := emptyFamily n) (h := h)
        (Rset := emptyRectangles n) = 0 := by
  classical
  simpa using
    (entropySurplus_eq_zero_of_allCovered (n := n)
      (F := emptyFamily n) (Rset := emptyRectangles n) (h := h)
      emptyFamily_allCovered)

example {n h : ℕ} :
    muLex (n := n) (F := emptyFamily n) (h := h)
        (emptyRectangles n) = (0, 0) := by
  classical
  simpa using
    (muLex_eq_zero_of_allCovered (n := n) (F := emptyFamily n)
      (Rset := emptyRectangles n) (h := h) emptyFamily_allCovered)

example {n h : ℕ} {F : Family n} {R₁ R₂ : Finset (Subcube n)}
    (hlt : supportMass (n := n) (F := F) (Rset := R₁) <
      supportMass (n := n) (F := F) (Rset := R₂)) :
    muLexOrder (muLex (n := n) (F := F) (h := h) R₁)
      (muLex (n := n) (F := F) (h := h) R₂) :=
  muLex_order_of_supportMass_lt (n := n) (F := F) (h := h)
    (R₁ := R₁) (R₂ := R₂) hlt

example {n h : ℕ} {F : Family n} {R₁ R₂ : Finset (Subcube n)}
    (hs : supportMass (n := n) (F := F) (Rset := R₁) =
      supportMass (n := n) (F := F) (Rset := R₂))
    (hlt : entropySurplus (n := n) (F := F) (h := h) (Rset := R₁) <
      entropySurplus (n := n) (F := F) (h := h) (Rset := R₂)) :
    muLexOrder (muLex (n := n) (F := F) (h := h) R₁)
      (muLex (n := n) (F := F) (h := h) R₂) :=
  muLex_order_of_entropy_lt (n := n) (F := F) (h := h)
    (R₁ := R₁) (R₂ := R₂) hs hlt

example {n h : ℕ} (F : Family n) :
    WellFounded fun R₁ R₂ : Finset (Subcube n) =>
      muLexOrder (muLex (n := n) (F := F) (h := h) R₁)
        (muLex (n := n) (F := F) (h := h) R₂) := by
  simpa using muLex_wf (n := n) (F := F) (h := h)

end Cover2Tests
